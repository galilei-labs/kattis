
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Baza" (open.kattis.com/problems/baza).                      *)
(*                                                                     *)
(*   input   N, then N database words (one per line), then Q, then Q   *)
(*           query words; words are lowercase, fewer than 30 letters.  *)
(*   output  one integer per query, one per line: the step count.      *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim is  *)
(* tools/kattis_shim.ml, the middle third is baza exactly as  *)
(* `make extract` produced it (marray route).  This part is the        *)
(* untrusted wrapper: read, convert, call once, print.                 *)
(*                                                                     *)
(* The whole of stdin is read in one go and scanned by hand into       *)
(* whitespace-separated tokens; words become Pstring.t (= string).     *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_token () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let start = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data start (!pos - start)
  in
  let next_int () = int_of_string (next_token ()) in
  let read_words () =
    let n = next_int () in
    let cells = Array.make (max n 0) (Pstring.unsafe_of_string "") in
    for i = 0 to n - 1 do
      cells.(i) <- Pstring.unsafe_of_string (next_token ())
    done;
    Arr.of_array cells (Pstring.unsafe_of_string "")
  in
  let db = read_words () in
  let qs = read_words () in
  let out = baza db qs in
  let q = Arr.length_to_int (Arr.length out) in
  let buf = Buffer.create (q * 8) in
  for i = 0 to q - 1 do
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get out (Uint63.of_int i)))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
