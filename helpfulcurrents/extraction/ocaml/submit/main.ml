
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Helpful Currents" (open.kattis.com/problems/helpfulcurrents)*)
(*                                                                     *)
(*   input   Y X x_init, then Y rows of X characters among ~ # @ > <   *)
(*           (row 0 the northernmost; the ship starts on row Y - 1).   *)
(*   output  the number of routes mod 1 000 003, or "begin repairs"    *)
(*           when there is none (the implem's None).                   *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (the shim and *)
(* the marray extraction verbatim).  This part is the untrusted        *)
(* wrapper: read, convert, call once, print.  Rows are read as tokens  *)
(* of non-blank characters (no map character is blank), so a stray     *)
(* '\r' is dropped; each becomes a Pstring.t (= OCaml string).         *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_blank c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let skip_blank () =
    while !pos < len && is_blank (String.unsafe_get data !pos) do incr pos done
  in
  let next_int () =
    skip_blank ();
    let v = ref 0 in
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c >= '0' && c <= '9'
    do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let next_token () =
    skip_blank ();
    let start = !pos in
    while !pos < len && not (is_blank (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data start (!pos - start)
  in
  let y = next_int () in
  let x = next_int () in
  let xi = next_int () in
  let rows = Array.init y (fun _ -> Pstring.unsafe_of_string (next_token ())) in
  let m = Arr.of_array rows (Pstring.unsafe_of_string "") in
  match
    helpfulcurrents (Uint63.of_int y) (Uint63.of_int x)
      (Uint63.of_int xi) m
  with
  | None -> print_string "begin repairs\n"
  | Some n ->
      print_string (string_of_int (snd (Uint63.to_int2 n)));
      print_char '\n'
