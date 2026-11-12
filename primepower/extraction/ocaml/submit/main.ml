
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Prime Powers" (open.kattis.com/problems/primepower).        *)
(*                                                                     *)
(*   input   three integers E, L, R, one per line                      *)
(*           (1 <= E <= 10^6, 1 <= L <= R <= 10^6).                    *)
(*   output  one line: the product of p^E over the primes p in [L, R], *)
(*           modulo 10^9 + 7.                                          *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml) and PrimepowerImpl exactly as `make extract` *)
(* produced it (marray route).  This part is the untrusted wrapper:    *)
(* read, convert, call once, print.  It does no arithmetic on the      *)
(* values; the result is already reduced modulo 10^9 + 7.             *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let next_int () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c < '0' || c > '9'
    do
      incr pos
    done;
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
  let e = next_int () in
  let l = next_int () in
  let r = next_int () in
  let o =
    primepower (Uint63.of_int e) (Uint63.of_int l)
      (Uint63.of_int r)
  in
  print_string (string_of_int (snd (Uint63.to_int2 o)));
  print_char '\n'
