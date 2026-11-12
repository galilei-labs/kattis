
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Derangement Rotations"                                      *)
(* (open.kattis.com/problems/derangementrotations).                    *)
(*                                                                     *)
(*   input   one line: n (3 <= n <= 10^6) and a prime p                *)
(*           (10^8 <= p <= 10^9+7).                                    *)
(*   output  one integer: the count of derangements D of size n with   *)
(*           f(D) = n - 2, modulo p.                                   *)
(*                                                                     *)
(* Untrusted wrapper: read, convert, call once, print.                 *)
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
  let r =
    derangement_rotations (Uint63.of_int n)
      (Uint63.of_int p)
  in
  print_string (string_of_int (snd (Uint63.to_int2 r)));
  print_char '\n'
