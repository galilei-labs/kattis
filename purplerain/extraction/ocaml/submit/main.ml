(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Purple Rain" (open.kattis.com/problems/purplerain).         *)
(*                                                                     *)
(*   input   one line: a string of n 'R'/'B' (1 <= n <= 10^5).         *)
(*   output  one line  i j : the 1-based first and last section.       *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim and     *)
(* PurplerainImpl as `make extract` produced it, marray route).  This  *)
(* part is the untrusted wrapper: read stdin at once, keep the run of  *)
(* 'R'/'B' characters (dropping surrounding whitespace / CR / LF),     *)
(* call once, print.  Pstring.t is OCaml's string.                     *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let is_rb c = c = 'R' || c = 'B' in
  let start = ref 0 in
  while !start < len && not (is_rb (String.unsafe_get data !start)) do
    incr start
  done;
  let stop = ref !start in
  while !stop < len && is_rb (String.unsafe_get data !stop) do
    incr stop
  done;
  let s = String.sub data !start (!stop - !start) in
  let (i, j) = purplerain (Pstring.unsafe_of_string s) in
  print_string (string_of_int (snd (Uint63.to_int2 i)));
  print_char ' ';
  print_string (string_of_int (snd (Uint63.to_int2 j)));
  print_char '\n'
