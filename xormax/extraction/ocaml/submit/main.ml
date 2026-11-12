
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Xor Maximization" (open.kattis.com/problems/xormax).        *)
(*                                                                     *)
(*   input   n (1 <= n <= 100 000), then n integers a_1 .. a_n,        *)
(*           each in [1, 10^18] (fits in a 63-bit word).               *)
(*   output  one line: the maximal xor-sum of a subset.                *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml, then xormax as *)
(* `make extract` produced it (marray route).  This part is the        *)
(* untrusted wrapper: read, convert, call once, print.                 *)
(* The whole of stdin is read at once and scanned by hand.             *)
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
  let r = xormax a in
  print_string (string_of_int (snd (Uint63.to_int2 r)));
  print_char '\n'
