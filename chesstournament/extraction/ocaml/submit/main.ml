
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Chess Tournament" (open.kattis.com/problems/chesstournament)*)
(*                                                                     *)
(*   input   N M, then M lines "K s L", s one of '>' or '='.           *)
(*   output  one word: consistent / inconsistent.                      *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (the shim     *)
(* tools/kattis_shim.ml, [Arr] the route's array module, and the       *)
(* extracted ChesstournamentImpl verbatim).  This part is the          *)
(* untrusted wrapper: the M lines become three parallel arrays ks,     *)
(* wins (true for '>', false for '='), ls, as the spec encodes them;   *)
(* one call; print the word.                                           *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let skip_ws () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c = ' ' || c = '\n' || c = '\r' || c = '\t'
    do
      incr pos
    done
  in
  let next_int () =
    skip_ws ();
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
  let next_sym () =
    skip_ws ();
    let c = if !pos < len then String.unsafe_get data !pos else '=' in
    incr pos;
    c = '>'
  in
  let n = next_int () in
  let m = next_int () in
  let ks = Array.make (max m 0) Uint63.zero in
  let wins = Array.make (max m 0) false in
  let ls = Array.make (max m 0) Uint63.zero in
  for j = 0 to m - 1 do
    ks.(j) <- Uint63.of_int (next_int ());
    wins.(j) <- next_sym ();
    ls.(j) <- Uint63.of_int (next_int ())
  done;
  let b =
    chess_consistent (Uint63.of_int n)
      (Arr.of_array ks Uint63.zero)
      (Arr.of_array wins false)
      (Arr.of_array ls Uint63.zero)
  in
  print_string (if b then "consistent\n" else "inconsistent\n")
