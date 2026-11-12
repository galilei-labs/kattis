# Public OCaml build support

These shared runtime files and the OCaml assembly rules in `scripts/` are
manually maintained, outside `public-export.json`. They mirror the private
repository's runtime and deterministic standalone assembly implementation.

Each problem exports its extraction directive, runtime/program/interface
references under `extraction/ocaml/snapshots/`, I/O harness at `submit/main.ml`,
and standalone program at `submit/<problem>.ml`. Dune compiles the extracted
library and standalone program and checks both against the references.

The `marray` and `arrays_bigint` routes retain their respective trusted runtime
mappings. Compilation and freshness checks are not proofs of extraction or
runtime correctness. Public builds do not include private samples, validators,
judge submission tools or credentials.
