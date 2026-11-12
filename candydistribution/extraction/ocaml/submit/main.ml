(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Candy Distribution" (open.kattis.com/problems/candydistribution). *)
(*                                                                     *)
(*   input   t (0 < t < 100), then t lines "K C", 1 <= K, C <= 10^9.    *)
(*   output  per case one line: a number of bags b, or IMPOSSIBLE.     *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim +       *)
(* CandydistributionImpl as `make extract` produced it).  This part is *)
(* the untrusted wrapper: read, convert, call once per case, print.    *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let next_int () =
    while
      !pos < len
      && (let c = String.unsafe_get data !pos in c < '0' || c > '9')
    do incr pos done;
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
  let t = next_int () in
  let buf = Buffer.create 4096 in
  for _ = 1 to t do
    let k = next_int () in
    let c = next_int () in
    (match candydistribution
             (Uint63.of_int k) (Uint63.of_int c) with
     | None -> Buffer.add_string buf "IMPOSSIBLE"
     | Some b -> Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 b))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
