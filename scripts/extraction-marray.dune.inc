; Included from <problem>/extraction/ocaml/dune with KATTIS_PROBLEM set.
; One maintained runtime, copied into this extraction's build directory.
(rule
 (action (copy ../../../runtime/ocaml/marray.ml marray.ml)))

(alias
 (name extract)
 (deps %{env:KATTIS_PROBLEM=}_extracted_marray.ml
       %{env:KATTIS_PROBLEM=}_extracted_marray.mli
       marray.ml))

; Separate rules let Dune report/promote every stale file in a single pass.
; Ordinary checks never modify snapshots; make update-snapshots opts in.
(rule
 (alias check-snapshot)
 (action
  (diff snapshots/%{env:KATTIS_PROBLEM=}_extracted_marray.ml
        %{env:KATTIS_PROBLEM=}_extracted_marray.ml)))

(rule
 (alias check-snapshot)
 (action
  (diff snapshots/%{env:KATTIS_PROBLEM=}_extracted_marray.mli
        %{env:KATTIS_PROBLEM=}_extracted_marray.mli)))

(rule
 (alias check-snapshot)
 (action (diff snapshots/marray.ml marray.ml)))
