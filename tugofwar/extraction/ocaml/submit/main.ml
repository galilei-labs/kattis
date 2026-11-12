(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Tug of War" (open.kattis.com/problems/tugofwar).            *)
(*                                                                     *)
(*   input   n (1 <= n <= 100), then n weights, one per line, each in  *)
(*           [1, 450].                                                 *)
(*   output  one line  a b : the two team totals, the lesser first.    *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and TugofwarImpl exactly   *)
(* as `make extract` produced it (marray route).  This part is the     *)
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
  let cells = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  let a = Arr.of_array cells Uint63.zero in
  let (x, y) = tugofwar a in
  print_string (string_of_int (snd (Uint63.to_int2 x)));
  print_char ' ';
  print_string (string_of_int (snd (Uint63.to_int2 y)));
  print_char '\n'
