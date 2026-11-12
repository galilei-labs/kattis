
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "String Multimatching" (stringmultimatching).               *)
(*                                                                     *)
(*   input   test cases until end of file; each: a line with n, then  *)
(*           n pattern lines, then one text line.  Patterns and text   *)
(*           may contain spaces, so the input is split on '\n' only    *)
(*           (a trailing '\r' is dropped).                             *)
(*   output  per case n lines: the 0-based positions of pattern i in   *)
(*           the text, ascending, separated by single spaces (an empty *)
(*           line when there is none).                                 *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* the marray extraction verbatim).  This part is the untrusted        *)
(* wrapper: read, convert, call once per case, print.                  *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* next line, without its '\n' and trailing '\r'; None at end of file *)
  let next_line () =
    if !pos >= len then None
    else begin
      let start = !pos in
      let e = match String.index_from_opt data start '\n' with
        | Some e -> e | None -> len in
      pos := e + 1;
      let stop = if e > start && data.[e - 1] = '\r' then e - 1 else e in
      Some (String.sub data start (stop - start))
    end
  in
  let out = Buffer.create (1 lsl 20) in
  let rec cases () =
    match next_line () with
    | None -> ()
    | Some l when String.trim l = "" -> cases ()
    | Some l ->
      let n = int_of_string (String.trim l) in
      let pats = Array.init n (fun _ ->
        match next_line () with
        | Some p -> Pstring.unsafe_of_string p
        | None -> Pstring.unsafe_of_string "") in
      let txt = match next_line () with Some t -> t | None -> "" in
      let res =
        multimatch
          (Arr.of_array pats (Pstring.unsafe_of_string ""))
          (Pstring.unsafe_of_string txt) in
      let m = Arr.length_to_int (Arr.length res) in
      for i = 0 to m - 1 do
        let row = Arr.get res (Uint63.of_int i) in
        let k = Arr.length_to_int (Arr.length row) in
        for j = 0 to k - 1 do
          if j > 0 then Buffer.add_char out ' ';
          Buffer.add_string out
            (string_of_int (snd (Uint63.to_int2 (Arr.get row (Uint63.of_int j)))))
        done;
        Buffer.add_char out '\n'
      done;
      cases ()
  in
  cases ();
  print_string (Buffer.contents out)
