(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Card Hand Sorting" (cardhand).                              *)
(*   input   n (1 <= n <= 52), then n distinct two-character cards.   *)
(*   output  one line: the least number of moves that sorts the hand. *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml and CardhandImpl exactly as extracted   *)
(* (marray route).  This part reads, converts, calls once, prints.     *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_token () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let start = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do incr pos done;
    String.sub data start (!pos - start)
  in
  let n = int_of_string (next_token ()) in
  let cards = Array.init n (fun _ -> Pstring.unsafe_of_string (next_token ())) in
  let a = Arr.of_array cards (Pstring.unsafe_of_string "") in
  let m = min_moves a in
  print_string (string_of_int (snd (Uint63.to_int2 m)));
  print_char '\n'
