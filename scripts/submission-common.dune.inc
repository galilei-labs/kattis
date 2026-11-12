; Route-independent standalone compilation, freshness, and sample checks.
(subdir submission-build
 (subdir submit
  (rule
   (target submission.exe)
   (deps (:source %{env:KATTIS_PROBLEM=}.ml))
   (action
    (run %{bin:ocamlopt} -o %{target}
     -I +unix -I +str unix.cmxa str.cmxa
     %{source})))))

(alias
 (name generate-submissions)
 (deps submission-build/submit/%{env:KATTIS_PROBLEM=}.ml))

(rule
 (alias check-submission)
 (action
  (diff submit/%{env:KATTIS_PROBLEM=}.ml
        submission-build/submit/%{env:KATTIS_PROBLEM=}.ml)))
