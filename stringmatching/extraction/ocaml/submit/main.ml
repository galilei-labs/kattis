
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "String Matching" (open.kattis.com/problems/stringmatching). *)
(*                                                                     *)
(*   input   test cases until end of file, each two lines: a pattern,  *)
(*           then a text (both may contain spaces; file <= 5 Mb).      *)
(*   output  per case one line: the 0-based positions of the pattern's *)
(*           occurrences in the text, ascending, single spaces (an     *)
(*           empty line when there is none).                           *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim +       *)
(* StringmatchingImpl as `make extract` produced it, marray route).    *)
(* This part is the untrusted wrapper: read, split lines, call once    *)
(* per case, print.  stdin is read in one go and split on '\n' by      *)
(* hand (a trailing '\r' is dropped); lines are passed as Pstring.t =  *)
(* OCaml string.                                                       *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* next line, without its '\n' (and a trailing '\r'); None at EOF *)
  let next_line () =
    if !pos >= len then None
    else begin
      let start = !pos in
      let stop =
        match String.index_from_opt data start '\n' with
        | Some j -> j
        | None -> len
      in
      pos := stop + 1;
      let e =
        if stop > start && String.unsafe_get data (stop - 1) = '\r'
        then stop - 1 else stop
      in
      Some (String.sub data start (e - start))
    end
  in
  let out = Buffer.create (1 lsl 20) in
  let rec loop () =
    match next_line () with
    | None -> ()
    | Some pat ->
      let txt = match next_line () with Some t -> t | None -> "" in
      let r =
        find_all
          (Pstring.unsafe_of_string pat) (Pstring.unsafe_of_string txt)
      in
      let k = Arr.length_to_int (Arr.length r) in
      for i = 0 to k - 1 do
        if i > 0 then Buffer.add_char out ' ';
        Buffer.add_string out
          (string_of_int (snd (Uint63.to_int2 (Arr.get r (Uint63.of_int i)))))
      done;
      Buffer.add_char out '\n';
      loop ()
  in
  loop ();
  print_string (Buffer.contents out)
