(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Zapis" (open.kattis.com/problems/zapis).                    *)
(*                                                                     *)
(*   input   N (even, 2 <= N <= 200), then the string of N characters  *)
(*           over ( ) [ ] { } ?.                                       *)
(*   output  one line: the number of regular completions, its last 5   *)
(*           digits (leading zeros kept) when it is at least 100000.   *)
(*                                                                     *)
(* The shim and zapis above come from the pipeline; this is  *)
(* the untrusted wrapper: read, call once, print.  The flag of the     *)
(* result says whether to pad the residue to 5 digits.                 *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* skip to N, read it *)
  while !pos < len && (data.[!pos] < '0' || data.[!pos] > '9') do incr pos done;
  let n = ref 0 in
  while !pos < len && data.[!pos] >= '0' && data.[!pos] <= '9' do
    n := (!n * 10) + Char.code data.[!pos] - 48;
    incr pos
  done;
  (* skip whitespace, then take the bracket string *)
  let is_br c =
    match c with
    | '(' | ')' | '[' | ']' | '{' | '}' | '?' -> true
    | _ -> false
  in
  while !pos < len && not (is_br data.[!pos]) do incr pos done;
  let start = !pos in
  while !pos < len && is_br data.[!pos] do incr pos done;
  let s = String.sub data start (!pos - start) in
  let (r, big) = zapis (Pstring.unsafe_of_string s) in
  let r = snd (Uint63.to_int2 r) in
  print_string (if big then Printf.sprintf "%05d" r else string_of_int r);
  print_char '\n'
