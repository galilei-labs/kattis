; Pair with ArraysStrong and [Set Rust Extraction Copy On Write Arrays.].
(rule
 (target rocq_array.rs)
 (action
  (copy %{read-lines:../../../runtime/rust/share-directory}/runtime/arrays/rocq_array_strong.rs
        %{target})))

(rule
 (target array-route)
 (action (with-stdout-to %{target} (echo strong-cow))))

(include submission-rust-common.dune.inc)
