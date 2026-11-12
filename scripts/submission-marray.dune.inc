; Included from <problem>/extraction/ocaml/dune with KATTIS_PROBLEM set.
; A virtual scratch directory avoids a target/source collision with submit/*.ml.
(subdir submission-build
 (subdir submit
  (rule
   (deps
    (:extracted ../../%{env:KATTIS_PROBLEM=}_extracted_marray.ml)
    (:main ../../submit/main.ml))
   (action
    (with-stdout-to %{env:KATTIS_PROBLEM=}.ml
     (run %{bin:python3}
      %{dep:../../../../../scripts/assemble-submission-ocaml.py}
      --problem %{env:KATTIS_PROBLEM=}
      --route marray
      --shim %{dep:../../../../../runtime/ocaml/kattis_shim.ml}
      --extracted %{extracted}
       --main %{main}))))))

(include submission-common.dune.inc)
