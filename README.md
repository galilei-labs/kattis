# Specifications and Verified Implementations for 100 Kattis problems

A collection of [Kattis](open.kattis.com) problems with formal specifications and Rocq implementations and correctness proofs.
We also provide snapshots of extracted Rust code.

See [our blogpost](http://galileilabs.com/research/kattis/).

Each problem includes:
- A `.spec` file containing its specification and accompanying documentation.
- A `_implem.v` file containing its implementation and proofs.
- A Rust extraction snapshot under `extraction/rust/snapshots/`.

The Rocq code relies on our internal libraries, which we do not make public at present.
The Rust extraction snapshots contain the direct extraction output without our runtime for Rocq's primitive types.
