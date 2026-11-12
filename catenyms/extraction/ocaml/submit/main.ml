
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Catenyms" (open.kattis.com/problems/catenyms).              *)
(*                                                                     *)
(*   input   t; then per test case n (3 <= n <= 1000) and n distinct   *)
(*           lower-case words of 1..20 letters, one per line.          *)
(*   output  per test case one line: the lexicographically smallest    *)
(*           compound catenym (words joined by '.'), or "***".         *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* CatenymsImpl as `make extract` produced it, then [Arr]).  This part *)
(* is the untrusted wrapper: read, convert, call once per case, print. *)
(* Words are Pstring.t = OCaml string.                                 *)
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
  let next_int () = int_of_string (next_token ()) in
  let out = Buffer.create (1 lsl 16) in
  let t = next_int () in
  for _ = 1 to t do
    let n = next_int () in
    let cells = Array.init n (fun _ -> Pstring.unsafe_of_string (next_token ())) in
    let a = Arr.of_array cells (Pstring.unsafe_of_string "") in
    (match catenyms a with
     | None -> Buffer.add_string out "***"
     | Some c ->
         let m = Arr.length_to_int (Arr.length c) in
         for i = 0 to m - 1 do
           if i > 0 then Buffer.add_char out '.';
           Buffer.add_string out (Pstring.to_string (Arr.get c (Uint63.of_int i)))
         done);
    Buffer.add_char out '\n'
  done;
  print_string (Buffer.contents out)
