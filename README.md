# Kattis examples

Each of the 100 problems has three source files:

- `<problem>.spec`: the formal specification and Focus documentation.
- `<problem>_implem.v`: the executable definitions and dependencies needed to define them, including termination lemmas.
- `<problem>_proofs.v`: the correctness proofs and their mathematical helpers; imports and re-exports the implementation.

Proofs required by a recursive definition remain with that definition to avoid a
circular dependency. Sections are kept intact so their local context and
implicit arguments retain their original meaning. Both files are listed in the
Focus implementation viewer.

Check all specifications and both Rocq files without creating build artifacts in
the working tree:

```sh
opam exec --switch=rocq-9.2 -- python3 scripts/check-rocq.py
# Or check selected problems:
opam exec --switch=rocq-9.2 -- python3 scripts/check-rocq.py cold polymul1
```

Requires `rocq-speck`, Flocq, and the sibling `kattis-private/lib` sources.
Use `--lib PATH` to override the library directory, or `--flocq PATH` to use a
locally built Flocq tree (the directory containing `Core/`). `--jobs` controls
parallel compilation. Specs with complexity requirements also use `lib/Cost.v`,
copied from `kattis-private/complexity/lib/Cost.v`, and rocq-speck's compiled
`Complexity` library. The checker defaults to the sibling rocq-speck build;
use `--complexity PATH` to override that location.

The checker compiles the declared specification and the available implementation
and proof modules. It does not establish that every specification obligation has
an implementation: polymul2's added `polymul_time` complexity requirement is not
yet proved by the existing correctness proof file.

This repository was previously named `tristan-kattis2`. Its local checkout is
`galilei/kattis`; the upstream benchmark repository is now
`galilei/kattis-private` (`galilei-labs/kattis-private` on GitHub).

## Cold

The documented `cold/cold.spec` preserves the current upstream specification.
`cold/cold_implem.v` is the top-level rocq-speck implementation from
`kattis-private/100_problems_run_new/cold/implem-rocq-1`, synced at upstream
commit `5de4caf8`. The implementation and its correctness proofs are separated into
`cold_implem.v` and `cold_proofs.v`.

Build and check the Rocq proof and OCaml extraction with:

```sh
opam exec --switch=rocq-9.2 -- make -C cold/extraction check
```

This requires the sibling `../kattis-private/lib` representation library.
Override `LIB` when building with a different checkout location.
The mutable-array extraction is not a verified extraction backend; it relies
on linear use of arrays.

Preview from the sibling Galilei tooling checkout:

```sh
cd ../focus
PORT=3001 uv run python scripts/serve.py ../kattis/cold
```

The local preview and page path is `/kattis/cold/`.
