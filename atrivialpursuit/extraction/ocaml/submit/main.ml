(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "A Trivial Pursuit" (open.kattis.com/problems/atrivialpursuit).*)
(*                                                                     *)
(*   input   P N M (1 <= P <= 10^18, 1 <= N, M <= 400), then N         *)
(*           integers G_i, then M integers L_i (1 <= G_i, L_i <= 10^18)*)
(*   output  one line: the number of sequences, modulo 10^9 + 7.       *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the route's array module) and    *)
(* atrivialpursuit exactly as `make extract`       *)
(* produced it.  This part is the untrusted wrapper: read, convert,    *)
(* call once, print.  Every value is <= 10^18 < 2^62, so it fits an    *)
(* OCaml int and Uint63.of_int is exact.                               *)
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
  let p = next_int () in
  let n = next_int () in
  let m = next_int () in
  let read_arr k =
    let cells = Array.make (max k 0) Uint63.zero in
    for i = 0 to k - 1 do
      cells.(i) <- Uint63.of_int (next_int ())
    done;
    Arr.of_array cells Uint63.zero
  in
  let gs = read_arr n in
  let ls = read_arr m in
  let o = atrivialpursuit (Uint63.of_int p) gs ls in
  print_string (string_of_int (snd (Uint63.to_int2 o)));
  print_char '\n'
