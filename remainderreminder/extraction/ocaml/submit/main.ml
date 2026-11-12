
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Remainder Reminder" (open.kattis.com/problems/              *)
(* remainderreminder).                                                 *)
(*                                                                     *)
(*   input   seven positive integers a b c d e f g: the sheet a x b,   *)
(*           the left-overs c d e (largest to third largest box) and   *)
(*           the inclusive range [f, g] of the number of books.        *)
(*   output  one line: the unique number of books.                     *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (the shim     *)
(* tools/kattis_shim.ml and RemainderreminderImpl as `make extract`    *)
(* produced it).  This part is the untrusted wrapper: read, convert,   *)
(* call once, print.  It does no arithmetic on the values.             *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let next_int () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c < '0' || c > '9'
    do
      incr pos
    done;
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
    Uint63.of_int !v
  in
  let a = next_int () in
  let b = next_int () in
  let c = next_int () in
  let d = next_int () in
  let e = next_int () in
  let f = next_int () in
  let g = next_int () in
  let n = remainderreminder a b c d e f g in
  print_string (string_of_int (snd (Uint63.to_int2 n)));
  print_char '\n'
