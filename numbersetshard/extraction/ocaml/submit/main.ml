(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Number Sets (Hard)" (open.kattis.com/problems/numbersetshard)*)
(*                                                                     *)
(*   input   C (<= 10), then C lines "A B P",                          *)
(*           1 <= A <= B <= 10^12, B <= A + 10^6, 2 <= P <= B.         *)
(*   output  one line "Case #k: Y" per test case.                      *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the marray extraction  *)
(* of NumbersetshardImpl verbatim.  This part is the untrusted         *)
(* wrapper: read, convert, call once per case, print.                  *)
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
  let c = next_int () in
  let buf = Buffer.create 256 in
  for k = 1 to c do
    let a = next_int () in
    let b = next_int () in
    let p = next_int () in
    let y =
      numbersets (Uint63.of_int a) (Uint63.of_int b)
        (Uint63.of_int p)
    in
    Buffer.add_string buf "Case #";
    Buffer.add_string buf (string_of_int k);
    Buffer.add_string buf ": ";
    Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 y)));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
