(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Join Strings" (open.kattis.com/problems/joinstrings).       *)
(*                                                                     *)
(*   input   N, then N lowercase strings (one per line), then N-1      *)
(*           lines "a b" (1-based).                                    *)
(*   output  the one remaining string, then a newline.                 *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml and the marray extraction verbatim.     *)
(* This part is the untrusted wrapper: read all of stdin, scan tokens  *)
(* by hand, convert (Pstring.unsafe_of_string, Uint63.of_int,          *)
(* Arr.of_array), call joinstrings once, print_string. *)
(* The indices are passed 1-based, as the spec keeps them.             *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_tok () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let st = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do incr pos done;
    String.sub data st (!pos - st)
  in
  let next_int () =
    while !pos < len && (let c = String.unsafe_get data !pos in c < '0' || c > '9') do incr pos done;
    let v = ref 0 in
    while !pos < len && (let c = String.unsafe_get data !pos in c >= '0' && c <= '9') do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let n = next_int () in
  let ss = Array.init n (fun _ -> Pstring.unsafe_of_string (next_tok ())) in
  let m = max (n - 1) 0 in
  let xa = Array.make m Uint63.zero and xb = Array.make m Uint63.zero in
  for i = 0 to m - 1 do
    xa.(i) <- Uint63.of_int (next_int ());
    xb.(i) <- Uint63.of_int (next_int ())
  done;
  let s = Arr.of_array ss (Pstring.unsafe_of_string "") in
  let a = Arr.of_array xa Uint63.zero in
  let b = Arr.of_array xb Uint63.zero in
  let r = joinstrings s a b in
  print_string (Pstring.to_string r);
  print_char '\n'
