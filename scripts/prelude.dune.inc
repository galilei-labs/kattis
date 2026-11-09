; Included from each problem's spec/dune; paths are relative to that directory.
(rule
 (target Prelude.v)
 (deps (glob_files ../*.spec))
 (action
  (with-stdout-to %{target}
   (run %{env:SPECK=rocq-speck} dump-spec --prelude %{deps}))))
