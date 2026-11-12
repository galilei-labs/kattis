; Included from <problem>/extraction/ocaml/dune with KATTIS_PROBLEM set.
; Arrays are inlined by extraction; only the bigint runtime needs a module.
(rule
 (action (copy ../../../runtime/ocaml/bigint.ml bigint.ml)))

(alias
 (name extract)
 (deps %{env:KATTIS_PROBLEM=}_extracted_arrays_bigint.ml
       %{env:KATTIS_PROBLEM=}_extracted_arrays_bigint.mli
       bigint.ml))

; Separate rules let Dune report/promote every stale file in a single pass.
; Ordinary checks never modify snapshots; make update-snapshots opts in.
(rule
 (alias check-snapshot)
 (action
  (diff snapshots/%{env:KATTIS_PROBLEM=}_extracted_arrays_bigint.ml
        %{env:KATTIS_PROBLEM=}_extracted_arrays_bigint.ml)))

(rule
 (alias check-snapshot)
 (action
  (diff snapshots/%{env:KATTIS_PROBLEM=}_extracted_arrays_bigint.mli
        %{env:KATTIS_PROBLEM=}_extracted_arrays_bigint.mli)))

(rule
 (alias check-snapshot)
 (action (diff snapshots/bigint.ml bigint.ml)))
