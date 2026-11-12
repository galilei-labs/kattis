# Public Rust build support

These manually maintained files are outside `public-export.json`. Problem files
are exported from the private repository; do not edit their generated references
here. The assembler and compactor in `scripts/` are maintained alongside this
runtime support and must agree with the private bundling implementation.

`dune` obtains runtime sources and their redistribution notice from the installed
`rust-verified-extraction` package. It does not require the compiler's source
checkout. `io.rs` contains shared input/output representation helpers, not problem
algorithms. Each exported route chooses its matching ordinary or strong CoW
runtime. The assembler rejects incompatible directives and enforces the source
size ceiling, preserving license notices and omitting known runtime test modules.

The checked-in standalone `.rs` programs already contain the runtime modules and
notices. They compile with `rustc --edition=2021` without opam, Cargo, or sibling
runtime files. Rebuilding them from Rocq requires the dependencies in `kattis.opam`.

Public checks compile both optimized and debug programs and compare fresh
extractions/bundles to their references. Private samples, validators and judge
submission scripts are not exported. In particular, this public build is not a
new Kattis run or a proof of compiler correctness. Strong CoW revokes old array
versions; it is not generally equivalent to persistent arrays.
