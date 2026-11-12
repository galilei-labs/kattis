; Included from <problem>/extraction/rust/dune.
(rule
 (targets %{env:KATTIS_PROBLEM=}_extracted.rs extract.vo extract.glob)
 (deps extract.v
       ../../%{env:KATTIS_PROBLEM=}_implem.vo
       ../../spec/Prelude.vo
       (package rust-verified-extraction))
 (action
  (run %{bin:rocq} compile -q -Q ../.. %{env:KATTIS_ROCQ_THEORY=} extract.v)))

(rule
 (target rocq_int63.rs)
 (action
  (copy %{read-lines:../../../runtime/rust/share-directory}/runtime/int63/rocq_int63.rs
        %{target})))

(rule
 (target LICENSE)
 (action
  (copy %{read-lines:../../../runtime/rust/share-directory}/runtime/LICENSE %{target})))

(alias
 (name extract-rust)
 (deps %{env:KATTIS_PROBLEM=}_extracted.rs rocq_int63.rs rocq_array.rs LICENSE))

(rule
 (alias check-rust-snapshot)
 (action
  (diff snapshots/%{env:KATTIS_PROBLEM=}_extracted.rs
        %{env:KATTIS_PROBLEM=}_extracted.rs)))
