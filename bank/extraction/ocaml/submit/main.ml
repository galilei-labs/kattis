
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Bank Queue" (open.kattis.com/problems/bank).                *)
(*                                                                     *)
(*   input   N T (1 <= N <= 10 000, 1 <= T <= 47), then N lines        *)
(*           c_i t_i (1 <= c_i <= 100 000, 0 <= t_i < T).              *)
(*   output  one line: the maximum total cash.                         *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the array module of the route)   *)
(* and bank exactly as `make extract` produced it.  This part *)
(* is the untrusted wrapper: read, convert, call once, print.  All     *)
(* values are non-negative and far below 2^62.                         *)
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
  let n = next_int () in
  let t = next_int () in
  let cash = Array.make (max n 0) Uint63.zero in
  let dl = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cash.(i) <- Uint63.of_int (next_int ());
    dl.(i) <- Uint63.of_int (next_int ())
  done;
  let r =
    bank (Uint63.of_int t)
      (Arr.of_array cash Uint63.zero)
      (Arr.of_array dl Uint63.zero)
  in
  print_string (string_of_int (snd (Uint63.to_int2 r)));
  print_char '\n'
