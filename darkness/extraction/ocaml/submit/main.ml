
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "The Darkness" (open.kattis.com/problems/darkness).           *)
(*                                                                     *)
(*   input   B, then H, then R C, then R lines of C digits (no spaces) *)
(*           giving the bulb strengths.                                *)
(*   output  one line: the least cost of the fencing, in pounds.       *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the marray extraction  *)
(* verbatim.  This part is the untrusted wrapper: read, convert, call  *)
(* once, print.  The grid goes in as an array of R rows, each an array *)
(* of C words (Arr.of_array of Arr.of_array rows).                     *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_digit c = c >= '0' && c <= '9' in
  let skip () =
    while !pos < len && not (is_digit (String.unsafe_get data !pos)) do
      incr pos
    done
  in
  let next_int () =
    skip ();
    let v = ref 0 in
    while !pos < len && is_digit (String.unsafe_get data !pos) do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let b = next_int () in
  let h = next_int () in
  let r = next_int () in
  let c = next_int () in
  let empty = Arr.of_array [||] Uint63.zero in
  let rows =
    Array.init r (fun _ ->
        skip ();
        let row =
          Array.init c (fun _ ->
              let d = Char.code (String.unsafe_get data !pos) - 48 in
              incr pos;
              Uint63.of_int d)
        in
        Arr.of_array row Uint63.zero)
  in
  let g = Arr.of_array rows empty in
  let o = darkness (Uint63.of_int b) (Uint63.of_int h) g in
  print_string (string_of_int (snd (Uint63.to_int2 o)));
  print_char '\n'
