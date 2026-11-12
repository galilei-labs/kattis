
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Water" (open.kattis.com/problems/water).                    *)
(*                                                                     *)
(*   input   n p k, then p lines "a b c" (initial pipes), then k lines *)
(*           "a b c" (improvements).                                   *)
(*   output  k+1 integers, one per line: the max flow from station 1   *)
(*           to station 2 initially and after each improvement.        *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* water as `make extract` produced it, then Arr).  This     *)
(* part is the untrusted wrapper: read, convert, call once, print.     *)
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
  let p = next_int () in
  let k = next_int () in
  let read_section m =
    let a = Array.make m Uint63.zero in
    let b = Array.make m Uint63.zero in
    let c = Array.make m Uint63.zero in
    for i = 0 to m - 1 do
      a.(i) <- Uint63.of_int (next_int ());
      b.(i) <- Uint63.of_int (next_int ());
      c.(i) <- Uint63.of_int (next_int ())
    done;
    (Arr.of_array a Uint63.zero, Arr.of_array b Uint63.zero,
     Arr.of_array c Uint63.zero)
  in
  let (pa, pb, pc) = read_section p in
  let (ia, ib, ic) = read_section k in
  let r = water (Uint63.of_int n) pa pb pc ia ib ic in
  let m = Arr.length_to_int (Arr.length r) in
  let buf = Buffer.create (m * 6) in
  for t = 0 to m - 1 do
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get r (Uint63.of_int t)))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
