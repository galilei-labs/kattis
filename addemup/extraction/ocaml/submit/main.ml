
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Add 'Em Up!" (open.kattis.com/problems/addemup).            *)
(*                                                                     *)
(*   input   n s, then n integers in [1, 100 000 000]                  *)
(*           (1 <= n <= 100 000, 2 <= s <= 200 000 000).               *)
(*   output  one line: YES or NO.                                      *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml) and addemup exactly as           *)
(* `make extract` produced it (marray route).  This part is the        *)
(* untrusted wrapper: read, convert, call once, print.                 *)
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
  let s = next_int () in
  let cells = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  let a = Arr.of_array cells Uint63.zero in
  print_string (if addemup (Uint63.of_int s) a then "YES" else "NO");
  print_char '\n'
