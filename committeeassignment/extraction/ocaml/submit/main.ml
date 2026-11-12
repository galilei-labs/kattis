
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Committee Assignment"                                       *)
(* (open.kattis.com/problems/committeeassignment).                     *)
(*                                                                     *)
(*   input   up to 50 departments: n m, then m lines "x y" (names of   *)
(*           up to 20 letters); ends with "0 0".                       *)
(*   output  one line per department: the minimum number of            *)
(*           committees.                                               *)
(*                                                                     *)
(* Everything above comes from the pipeline (shim + extracted code,    *)
(* marray route).  This part is the untrusted wrapper: read the whole  *)
(* of stdin, split into whitespace-separated tokens, build the two     *)
(* name columns as Pstring arrays, call committees once per department *)
(* and print.                                                          *)
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
  let next_int () =
    let t = next_token () in
    if t = "" then 0 else int_of_string t
  in
  let out = Buffer.create 256 in
  let rec loop () =
    let n = next_int () in
    let m = next_int () in
    if n <> 0 || m <> 0 then begin
      let ca = Array.make m "" and cb = Array.make m "" in
      for i = 0 to m - 1 do
        ca.(i) <- next_token ();
        cb.(i) <- next_token ()
      done;
      let empty = Pstring.unsafe_of_string "" in
      let a = Arr.of_array (Array.map Pstring.unsafe_of_string ca) empty in
      let b = Arr.of_array (Array.map Pstring.unsafe_of_string cb) empty in
      let k = committees (Uint63.of_int n) a b in
      Buffer.add_string out (string_of_int (snd (Uint63.to_int2 k)));
      Buffer.add_char out '\n';
      loop ()
    end
  in
  loop ();
  print_string (Buffer.contents out)
