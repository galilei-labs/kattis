(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Babelfish" (open.kattis.com/problems/babelfish).            *)
(*                                                                     *)
(*   input   lines "english foreign" (up to 100 000), a blank line,    *)
(*           then the message, one foreign word per line.              *)
(*   output  the English word of each message word, or "eh".           *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted code of  *)
(* the route.  This part is the untrusted wrapper: read, split, call   *)
(* babelfish once, print.  Strings are Pstring.t, i.e.   *)
(* OCaml strings.  '\r' is treated as whitespace.                      *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_ws c = c = ' ' || c = '\r' || c = '\t' in
  (* Dictionary: lines up to the first line with no word on it. *)
  let eng = ref [] and frn = ref [] in
  let continue = ref true in
  while !continue && !pos < len do
    let eol = match String.index_from_opt data !pos '\n' with
      | Some k -> k | None -> len in
    let i = ref !pos in
    let word () =
      while !i < eol && is_ws (String.unsafe_get data !i) do incr i done;
      let s = !i in
      while !i < eol && not (is_ws (String.unsafe_get data !i)) do incr i done;
      String.sub data s (!i - s)
    in
    let e = word () in
    if e = "" then continue := false
    else begin
      let f = word () in
      eng := Pstring.unsafe_of_string e :: !eng;
      frn := Pstring.unsafe_of_string f :: !frn
    end;
    pos := eol + 1
  done;
  (* Message: every remaining word. *)
  let msg = ref [] in
  while !pos < len do
    while !pos < len && (let c = String.unsafe_get data !pos in
                         is_ws c || c = '\n') do incr pos done;
    let s = !pos in
    while !pos < len && (let c = String.unsafe_get data !pos in
                         not (is_ws c || c = '\n')) do incr pos done;
    if !pos > s then
      msg := Pstring.unsafe_of_string (String.sub data s (!pos - s)) :: !msg
  done;
  let arr l = Arr.of_array (Array.of_list (List.rev l)) "" in
  let out = babelfish (arr !eng) (arr !frn) (arr !msg) in
  let n = Arr.length_to_int (Arr.length out) in
  let b = Buffer.create (12 * n + 16) in
  for k = 0 to n - 1 do
    (match Arr.get out (Uint63.of_int k) with
     | Some w -> Buffer.add_string b (Pstring.to_string w)
     | None -> Buffer.add_string b "eh");
    Buffer.add_char b '\n'
  done;
  print_string (Buffer.contents b)
