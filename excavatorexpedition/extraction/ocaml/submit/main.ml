
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Excavator Expedition" (open.kattis.com/problems/            *)
(* excavatorexpedition).                                               *)
(*                                                                     *)
(*   input   V E; a line of V characters ('X' or '.'); E lines F T.    *)
(*   output  one integer, the best happiness (possibly negative).      *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted          *)
(* ExcavatorexpeditionImpl (marray route).  This part is the untrusted *)
(* wrapper: read, convert, call once, print.  The site line is passed  *)
(* as a Pstring (OCaml string), the edges as two arrays of words; the  *)
(* answer is a signed word read back with [snd (Uint63.to_int2 _)].    *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let skip_blank () =
    while !pos < len && (match String.unsafe_get data !pos with
                         | ' ' | '\n' | '\r' | '\t' -> true | _ -> false)
    do incr pos done
  in
  let next_int () =
    skip_blank ();
    let v = ref 0 in
    while
      !pos < len
      && (let c = String.unsafe_get data !pos in c >= '0' && c <= '9')
    do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let v = next_int () in
  let e = next_int () in
  skip_blank ();
  let sites = String.sub data !pos v in
  pos := !pos + v;
  let src = Array.make e Uint63.zero in
  let dst = Array.make e Uint63.zero in
  for k = 0 to e - 1 do
    src.(k) <- Uint63.of_int (next_int ());
    dst.(k) <- Uint63.of_int (next_int ())
  done;
  let h =
    excavator (Pstring.unsafe_of_string sites)
      (Arr.of_array src Uint63.zero) (Arr.of_array dst Uint63.zero)
  in
  print_string (string_of_int (snd (Uint63.to_int2 h)));
  print_char '\n'
