
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Chicken Joggers" (open.kattis.com/problems/joggers).        *)
(*                                                                     *)
(*   input   N S; then N-1 lines "a b d"; then L; then L lamp ids.     *)
(*   output  one integer: the least number of new lamps.               *)
(*                                                                     *)
(* Everything above this comment is the shim and the extracted code   *)
(* (route marray: joggers).  This part reads all of stdin, *)
(* scans by hand, converts, calls once and prints.                     *)
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
  let m = max (n - 1) 0 in
  let a = Array.make m Uint63.zero in
  let b = Array.make m Uint63.zero in
  let d = Array.make m Uint63.zero in
  for j = 0 to m - 1 do
    a.(j) <- Uint63.of_int (next_int ());
    b.(j) <- Uint63.of_int (next_int ());
    d.(j) <- Uint63.of_int (next_int ())
  done;
  let nl = next_int () in
  let l = Array.make (max nl 0) Uint63.zero in
  for i = 0 to nl - 1 do
    l.(i) <- Uint63.of_int (next_int ())
  done;
  let r =
    joggers (Uint63.of_int n) (Uint63.of_int s)
      (Arr.of_array a Uint63.zero) (Arr.of_array b Uint63.zero)
      (Arr.of_array d Uint63.zero) (Arr.of_array l Uint63.zero)
  in
  print_string (string_of_int (snd (Uint63.to_int2 r)));
  print_char '\n'
