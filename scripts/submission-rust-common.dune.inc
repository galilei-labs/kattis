; Public build support: regenerate, compile and compare, without private samples.
(subdir submission-build
 (subdir submit
  (rule
   (target %{env:KATTIS_PROBLEM=}.rs)
   (deps
    (:extracted ../../%{env:KATTIS_PROBLEM=}_extracted.rs)
    (:directives ../../extract.v)
    (:harness ../../harness.rs)
    (:int63 ../../rocq_int63.rs)
    (:arrays ../../rocq_array.rs)
    (:license ../../LICENSE)
    (:route ../../array-route)
    ../../../../../scripts/compact_rust_source.py)
   (action
    (with-stdout-to %{target}
     (run %{bin:python3}
      %{dep:../../../../../scripts/assemble-submission-rust.py}
      --problem %{env:KATTIS_PROBLEM=}
      --array-route %{read-lines:../../array-route}
      --directives %{directives} --extracted %{extracted}
      --harness %{harness} --int63 %{int63} --arrays %{arrays}
      --license %{license}
      --bigint %{dep:../../../../../runtime/rust/rocq_bigint.rs}
      --float64 %{dep:../../../../../runtime/rust/rocq_float64.rs}
      --string %{dep:../../../../../runtime/rust/rocq_string.rs}
      --io-helpers %{dep:../../../../../runtime/rust/io.rs}))))
  (rule
   (target submission.exe)
   (deps (:source %{env:KATTIS_PROBLEM=}.rs))
   (action
    (run %{bin:rustc} --edition=2021 -A warnings -O %{source} -o %{target})))
  (rule
   (target submission-debug.exe)
   (deps (:source %{env:KATTIS_PROBLEM=}.rs))
   (action
    (run %{bin:rustc} --edition=2021 -A warnings %{source} -o %{target})))))

(alias
 (name generate-rust-submissions)
 (deps submission-build/submit/%{env:KATTIS_PROBLEM=}.rs))

(rule
 (alias check-rust-submission)
 (action
  (diff submit/%{env:KATTIS_PROBLEM=}.rs
        submission-build/submit/%{env:KATTIS_PROBLEM=}.rs)))
