
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Median" (open.kattis.com/problems/median).                  *)
(*                                                                     *)
(*   input   n (1 <= n <= 10^5), then n integers in [0, 10^9].         *)
(*   output  the median: an integer, or an integer plus one half.      *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* median as `make extract` produced it, then [Arr]).  This *)
(* part reads all of stdin, scans it by hand, calls the extracted      *)
(* function once, and prints its float r: twice r is an exact integer *)
(* t (at most 2*10^9); t even prints t/2, t odd prints t/2 then ".5"   *)
(* (the statement's samples print integers without decimals).          *)
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
  let r = Float64.to_float (median a) in
  let t = int_of_float (2.0 *. r) in
  print_string (string_of_int (t / 2));
  if t land 1 = 1 then print_string ".5";
  print_char '\n'
