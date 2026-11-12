
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Is-A? Has-A? Who Knowz-A?" (open.kattis.com/problems/      *)
(* isahasa).                                                           *)
(*                                                                     *)
(*   input   n m, then n lines "c1 r c2" (the given relationships),   *)
(*           then m lines of the same form (the queries); r is "is-a" *)
(*           or "has-a", class names are single words.                *)
(*   output  one line per query: "Query j: true" or "Query j: false". *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then  *)
(* isahasa as `make extract` produced it, marray route).  *)
(* This part is the untrusted wrapper: read all of stdin, split on    *)
(* whitespace, build the six parallel arrays (names are Pstring.t =   *)
(* OCaml strings), call once, print through a Buffer.                 *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_word () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let start = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data start (!pos - start)
  in
  let n = int_of_string (next_word ()) in
  let m = int_of_string (next_word ()) in
  let kind s = if s = "is-a" then IsA else HasA in
  let read k =
    let a = Array.make k "" and r = Array.make k IsA and b = Array.make k "" in
    for i = 0 to k - 1 do
      a.(i) <- next_word ();
      r.(i) <- kind (next_word ());
      b.(i) <- next_word ()
    done;
    let ps x = Arr.of_array (Array.map Pstring.unsafe_of_string x)
                 (Pstring.unsafe_of_string "") in
    (ps a, Arr.of_array r IsA, ps b)
  in
  let (src, rs, dst) = read n in
  let (qsrc, qrs, qdst) = read m in
  let o = isahasa src rs dst qsrc qrs qdst in
  let buf = Buffer.create (m * 20) in
  for j = 0 to m - 1 do
    Buffer.add_string buf "Query ";
    Buffer.add_string buf (string_of_int (j + 1));
    Buffer.add_string buf
      (if Arr.get o (Uint63.of_int j) then ": true\n" else ": false\n")
  done;
  print_string (Buffer.contents buf)
