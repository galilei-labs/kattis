
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Bitwise" (open.kattis.com/problems/bitwise).                *)
(*                                                                     *)
(*   input   N K (1 <= K <= N <= 5e5), then A_1 .. A_N in [0, 1e9].    *)
(*   output  one line: the maximum AND of the sections' ORs.           *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml, then BitwiseImpl exactly as            *)
(* `make extract` produced it (marray route).  This part is the        *)
(* untrusted wrapper: read, convert, call once, print.                 *)
(* All of stdin is read at once and scanned by hand (no Scanf).        *)
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
  let k = next_int () in
  let cells = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  let a = Arr.of_array cells Uint63.zero in
  let r = best_and (Uint63.of_int k) a in
  print_string (string_of_int (snd (Uint63.to_int2 r)));
  print_char '\n'
