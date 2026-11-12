
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Magic Sequence" (open.kattis.com/problems/magicsequence).   *)
(*                                                                     *)
(*   input   TC, then per test case: N; A B C; X Y (all positive,      *)
(*           N <= 10^6, the others <= 10^9).                           *)
(*   output  one line per test case: the hash V of the sorted S.       *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted code of  *)
(* the marray route verbatim.  This part is the untrusted wrapper:     *)
(* read, convert, call magic once per case, print.   *)
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
    !v
  in
  let tc = next_int () in
  let buf = Buffer.create 512 in
  for _ = 1 to tc do
    let n = next_int () in
    let a = next_int () in
    let b = next_int () in
    let c = next_int () in
    let x = next_int () in
    let y = next_int () in
    let u = Uint63.of_int in
    let v =
      magic (u n) (u a) (u b) (u c) (u x) (u y)
    in
    Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 v)));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
