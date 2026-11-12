
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Maze Movement" (open.kattis.com/problems/mazemovement).     *)
(*                                                                     *)
(*   input   n (2 <= n <= 1000), then n distinct room numbers, each in *)
(*           [2, 2*10^9], one per line.                                *)
(*   output  one integer: the maximum flow from the lowest-numbered    *)
(*           room to the highest-numbered one.                         *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* mazemovement as `make extract` produced it).  This *)
(* part is the untrusted wrapper: read, convert, call once, print.     *)
(* The rooms array is passed as is, in input order.                    *)
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
  let ans = mazemovement a in
  print_string (string_of_int (snd (Uint63.to_int2 ans)));
  print_char '\n'
