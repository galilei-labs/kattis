
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Canonical Coin Systems" (open.kattis.com/problems/canonical)*)
(*                                                                     *)
(*   input   n (2 <= n <= 100), then n denominations                   *)
(*           1 = c_1 < c_2 < ... < c_n <= 10^6.                        *)
(*   output  one line: "canonical" or "non-canonical".                 *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the array module of the route)   *)
(* and canonical exactly as `make extract` produced it.  *)
(* This part is the untrusted wrapper: read, convert, call once,       *)
(* print.  All input values are non-negative.                          *)
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
  let cells = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  let a = Arr.of_array cells Uint63.zero in
  print_string
    (if canonical a then "canonical\n" else "non-canonical\n")
