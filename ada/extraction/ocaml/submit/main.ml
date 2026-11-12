
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "The Calculus of Ada" (open.kattis.com/problems/ada).        *)
(*                                                                     *)
(*   input   one line: n (2 <= n <= 10), then n integers v_1 .. v_n,   *)
(*           each in [-2 000 000, 2 000 000], at least two distinct.   *)
(*   output  one line  d w : d the minimal degree, w the next value.   *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim is  *)
(* tools/kattis_shim.ml (the Rocq kernel's Uint63 and Parray, plus     *)
(* Marray; [Arr] names the one the route uses) and the middle third is *)
(* ada exactly as `make extract` produced it.  This part is    *)
(* the untrusted wrapper: read, convert, call once, print.  It does no *)
(* arithmetic on the values.                                           *)
(*                                                                     *)
(* The whole of stdin is read in one go and scanned by hand.  A        *)
(* negative value goes through Uint63.of_int (the identity on OCaml's  *)
(* int) and lands on the word whose signed reading is that number; the *)
(* answer's w is read back the same way, with [snd (Uint63.to_int2 _)].*)
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
      c <> '-' && (c < '0' || c > '9')
    do
      incr pos
    done;
    let neg = !pos < len && String.unsafe_get data !pos = '-' in
    if neg then incr pos;
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
    if neg then - !v else !v
  in
  let n = next_int () in
  let cells = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  (* Arr.of_array copies [cells]; the implem copies again before writing. *)
  let a = Arr.of_array cells Uint63.zero in
  let (d, w) = ada a in
  print_string (string_of_int (Uint63.to_int_min d max_int));
  print_char ' ';
  print_string (string_of_int (snd (Uint63.to_int2 w)));
  print_char '\n'
