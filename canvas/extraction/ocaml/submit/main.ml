
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Canvas Painting" (open.kattis.com/problems/canvas).         *)
(*                                                                     *)
(*   input   T (1 <= T <= 100), then per test case N (1 <= N <=         *)
(*           100 000) and N sizes in [1, 100 000]; sum of N <= 100 000. *)
(*   output  one line per test case: the minimum ink.                  *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml) and canvas exactly as `make       *)
(* extract` produced it (marray route).  This part is the untrusted    *)
(* wrapper: read, convert, call once per test case, print.  The answer *)
(* is at most about 1.7e11, far below 2^62, so it reads back exactly.  *)
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
  let t = next_int () in
  let buf = Buffer.create (t * 16) in
  for _ = 1 to t do
    let n = next_int () in
    let cells = Array.make (max n 0) Uint63.zero in
    for i = 0 to n - 1 do
      cells.(i) <- Uint63.of_int (next_int ())
    done;
    let a = Arr.of_array cells Uint63.zero in
    let r = canvas a in
    Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 r)));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
