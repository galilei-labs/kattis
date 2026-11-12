
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Pascal" (open.kattis.com/problems/pascal).                  *)
(*                                                                     *)
(*   input   one line: N, 1 <= N <= 10^9.                              *)
(*   output  one line: the counter Frane's program prints.             *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim is  *)
(* tools/kattis_shim.ml and the middle third is pascal      *)
(* exactly as `make extract` produced it (marray route; no array is    *)
(* used).  This part is the untrusted wrapper: read, convert, call     *)
(* once, print.  It does no arithmetic on the value.                   *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  while !pos < len && (let c = String.unsafe_get data !pos in c < '0' || c > '9') do
    incr pos
  done;
  let v = ref 0 in
  while !pos < len && (let c = String.unsafe_get data !pos in c >= '0' && c <= '9') do
    v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
    incr pos
  done;
  let r = pascal (Uint63.of_int !v) in
  print_string (string_of_int (snd (Uint63.to_int2 r)));
  print_char '\n'
