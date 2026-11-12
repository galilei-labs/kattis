
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Another Substring Query Problem"                           *)
(* (open.kattis.com/problems/anothersubstringqueryproblem).            *)
(*                                                                     *)
(*   input   s (lower-case, 1 <= |s| <= 2e5); q; then q lines "t k".   *)
(*   output  one line per query: 1-based start of the k-th occurrence  *)
(*           of t in s, or -1.                                         *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* the extracted code verbatim, then [module Arr = ...]).  This part   *)
(* is the untrusted wrapper: read, convert, call once, print.  The     *)
(* query lines become the two parallel columns ts (patterns) and ks    *)
(* (ranks) of the spec's kth_occurrences.  Answers are sint: read back *)
(* with [snd (Uint63.to_int2 _)] so that -1 prints as -1.             *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let skip () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done
  in
  let next_word () =
    skip ();
    let start = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data start (!pos - start)
  in
  let next_int () =
    skip ();
    let v = ref 0 in
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c >= '0' && c <= '9'
    do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let s = Pstring.unsafe_of_string (next_word ()) in
  let q = next_int () in
  let empty = Pstring.unsafe_of_string "" in
  let ts = Array.make (max q 0) empty in
  let ks = Array.make (max q 0) Uint63.zero in
  for i = 0 to q - 1 do
    ts.(i) <- Pstring.unsafe_of_string (next_word ());
    ks.(i) <- Uint63.of_int (next_int ())
  done;
  let o =
    kth_occurrences s
      (Arr.of_array ts empty) (Arr.of_array ks Uint63.zero)
  in
  let buf = Buffer.create (8 * (max q 1)) in
  let n = snd (Uint63.to_int2 (Arr.length o)) in
  for i = 0 to n - 1 do
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get o (Uint63.of_int i)))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
