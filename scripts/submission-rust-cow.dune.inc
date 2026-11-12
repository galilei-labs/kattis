; Pair with Arrays and [Set Rust Extraction Copy On Write Arrays.] in extract.v.
(rule
 (target rocq_array.rs)
 (action
  (copy %{read-lines:../../../runtime/rust/share-directory}/runtime/arrays/rocq_array_cow.rs
        %{target})))

(rule
 (target array-route)
 (action (with-stdout-to %{target} (echo cow))))

(include submission-rust-common.dune.inc)
