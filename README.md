# Kattis examples

One documented specification per problem, with the `cold` example also including
its Rocq implementation, extracted OCaml code and generated web page.

This repository was previously named `tristan-kattis2`. Its local checkout is
`galilei/kattis`; the upstream benchmark repository is now
`galilei/kattis-private` (`galilei-labs/kattis-private` on GitHub).

## Cold

The documented `cold/cold.spec` preserves the current upstream specification.
`cold/cold_implem.v` is the top-level rocq-speck implementation from
`kattis-private/100_problems_run_new/cold/implem-rocq-1`, synced at upstream
commit `5de4caf8`. The proofs now live alongside the implementation, as upstream.

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
