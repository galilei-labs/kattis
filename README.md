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

Each of the 100 problems has three source files:

- `<problem>.spec`: the formal specification and Focus documentation.
- `<problem>_implem.v`: executable definitions, including termination lemmas.
- `<problem>_proofs.v`: correctness proofs and mathematical helpers; re-exports
  the implementation.

Both Rocq files are listed in the Focus implementation viewer. Checked-in OCaml
snapshots live in each problem's `extraction/ocaml/` directory.

## Build

The root Dune project (Rocq language 0.11) builds 99 problems. `polymul2`
is excluded pending the shared Cost/Complexity library setup.

```sh
opam exec -- make build       # Build all Dune-enabled problems
opam exec -- make cold        # Build Cold only
opam exec -- make clean       # Remove the shared _build/ directory
```

Equivalently, use `dune build`, or `dune build <problem>` for one problem.
Each build generates a Prelude from the specification and compiles the
implementation and correctness proofs. Preludes use problem-specific namespaces,
e.g. `Arbitrage.spec.Prelude`; their generation rule is shared in
`scripts/prelude.dune.inc`. All generated and compiled artifacts stay under
`_build/`.

Cold additionally generates and compiles fresh OCaml extraction, including its
interface. Other problems currently have only checked-in OCaml snapshots, not
extraction drivers; those snapshots are unchanged by Dune builds.

**These builds do not run `rocq-speck check`.** Compilation checks the supplied
proofs, but does not establish that every specification obligation is implemented
or enforce the specification's allowed-axiom policy.

### Alternative compilation checker

The Python checker compiles the generated Prelude, implementation and proofs in
temporary directories, with up to four problems in parallel:

```sh
opam exec -- python3 scripts/check-rocq.py cold polymul1
```

It uses the active switch's dependencies. `--jobs N` controls parallelism;
`--flocq PATH` selects a locally built Flocq tree containing `Core/`.

Like Dune, this script does **not** run `rocq-speck check`. Without problem names
it attempts all 100 problems, including `polymul2`, whose legacy Cost/Complexity
setup is not yet supported by the standard build. Its `polymul_time` obligation
also remains unproved.

## OCaml extraction

Each problem has a checked-in OCaml snapshot under `extraction/ocaml/`.
Regeneration is currently wired into Dune only for Cold; other problems' snapshots
are not rebuilt. Their extraction drivers will be imported from `kattis-private`
separately. Fresh output stays under `_build/` until explicitly promoted.

For Cold, generate fresh OCaml and compile it against its interface:

```sh
opam exec -- make -C cold/extraction check
```

Cold's `all`, `marray`, `check`, and `clean` Makefile targets delegate to
the root Dune project. `marray` generates fresh OCaml from the implementation;
`check` also compiles the generated `.ml` against its `.mli`. Use the full build
to check correctness proofs as well.
Neither overwrites the checked-in OCaml snapshot in `cold/extraction/ocaml/`.
`clean` removes the shared workspace build directory.

Compare fresh output with the tracked snapshot (Cold example):

```sh
opam exec -- dune build @cold/extraction/check-snapshot
```

If it reports differences, update the snapshot explicitly with:

```sh
opam exec -- dune promote \
  cold/extraction/ocaml/cold_extracted_marray.ml \
  cold/extraction/ocaml/cold_extracted_marray.mli \
  cold/extraction/ocaml/marray.ml
```

Review the resulting Git diff. Ordinary builds do not update snapshots.

The mutable-array extraction is not a verified extraction backend; it relies
on linear use of arrays.

## Preview

Preview from the sibling Galilei tooling checkout:

```sh
cd ../focus
PORT=3001 uv run python scripts/serve.py ../kattis/cold
```

The local preview and page path is `/kattis/cold/`.

## Upstream

These examples originate from
[`galilei-labs/kattis-private`](https://github.com/galilei-labs/kattis-private).
This repository was previously named `tristan-kattis2`.
