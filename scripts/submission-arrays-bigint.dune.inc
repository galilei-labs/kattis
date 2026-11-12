; Included from <problem>/extraction/ocaml/dune with KATTIS_PROBLEM set.
(subdir submission-build
 (subdir submit
  (rule
   (deps
    (:extracted ../../%{env:KATTIS_PROBLEM=}_extracted_arrays_bigint.ml)
    (:main ../../submit/main.ml))
   (action
    (with-stdout-to %{env:KATTIS_PROBLEM=}.ml
     (run %{bin:python3}
      %{dep:../../../../../scripts/assemble-submission-ocaml.py}
      --problem %{env:KATTIS_PROBLEM=}
      --route arrays_bigint
      --shim %{dep:../../../../../runtime/ocaml/kattis_shim.ml}
      --bigint %{dep:../../../../../runtime/ocaml/bigint.ml}
      --extracted %{extracted}
      --main %{main}))))))

(include submission-common.dune.inc)
