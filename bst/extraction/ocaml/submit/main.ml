
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Binary search tree" (open.kattis.com/problems/bst).         *)
(*                                                                     *)
(*   input   N (1 <= N <= 300 000), then N distinct integers in [1,N], *)
(*           one per line.                                             *)
(*   output  N lines: the counter C after each insertion.              *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim is  *)
(* tools/kattis_shim.ml and the middle third is bst exactly as *)
(* `make extract` produced it (marray route).  This part is the        *)
(* untrusted wrapper: read, convert, call once, print.  C is at most   *)
(* N(N-1)/2 < 2^62, read back with [snd (Uint63.to_int2 _)].           *)
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
  let c = bst a in
  let m = Arr.length_to_int (Arr.length c) in
  let buf = Buffer.create (m * 12 + 16) in
  for i = 0 to m - 1 do
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get c (Uint63.of_int i)))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
