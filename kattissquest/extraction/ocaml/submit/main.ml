
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Kattis's Quest" (open.kattis.com/problems/kattissquest).    *)
(*                                                                     *)
(*   input   N (1 <= N <= 2*10^5), then N lines "add E G" or           *)
(*           "query X" (1 <= E, G, X <= 10^5).                         *)
(*   output  one line per query: the gold earned, in order.            *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml), the marray extraction verbatim, and         *)
(* [module Arr = Marray].  This part is the untrusted wrapper: read,   *)
(* build the [command] array (Add / Query of the extracted code), call *)
(* once, print.  Stdin is read in one go and scanned by hand.          *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let skip_blank () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c = ' ' || c = '\n' || c = '\r' || c = '\t'
    do
      incr pos
    done
  in
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
    !v
  in
  (* Skip the command word; return its first letter. *)
  let next_word () =
    skip_blank ();
    let c = if !pos < len then String.unsafe_get data !pos else ' ' in
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c >= 'a' && c <= 'z'
    do
      incr pos
    done;
    c
  in
  let n = next_int () in
  let dummy = Query Uint63.zero in
  let cells = Array.make (max n 0) dummy in
  for i = 0 to n - 1 do
    if next_word () = 'a' then begin
      let e = next_int () in
      let g = next_int () in
      cells.(i) <- Add (Uint63.of_int e, Uint63.of_int g)
    end else
      cells.(i) <- Query (Uint63.of_int (next_int ()))
  done;
  let a = Arr.of_array cells dummy in
  let r = kattissquest a in
  let m = Arr.length_to_int (Arr.length r) in
  let buf = Buffer.create (8 * (m + 1)) in
  for i = 0 to m - 1 do
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get r (Uint63.of_int i)))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
