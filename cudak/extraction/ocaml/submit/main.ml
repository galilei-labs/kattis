
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Cudak" (open.kattis.com/problems/cudak).                    *)
(*                                                                     *)
(*   input   three integers A B S, 1 <= A <= B < 10^15, 1 <= S <= 135. *)
(*   output  two lines: the count of integers in [A, B] with digit sum *)
(*           S, then the smallest such integer.                        *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim is  *)
(* tools/kattis_shim.ml and the middle third is cudak exactly *)
(* as `make extract` produced it.  This part is the untrusted wrapper: *)
(* read, convert, call once, print.  The values (< 10^15) fit an OCaml *)
(* int and a 63-bit word.                                              *)
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
  let a = next_int () in
  let b = next_int () in
  let s = next_int () in
  let (cnt, m) =
    cudak (Uint63.of_int a) (Uint63.of_int b) (Uint63.of_int s)
  in
  print_string (string_of_int (snd (Uint63.to_int2 cnt)));
  print_char '\n';
  print_string (string_of_int (snd (Uint63.to_int2 m)));
  print_char '\n'
