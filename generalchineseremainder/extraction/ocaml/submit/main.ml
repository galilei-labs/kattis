
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Chinese Remainder Theorem (non-relatively prime moduli)"    *)
(* (open.kattis.com/problems/generalchineseremainder).                 *)
(*                                                                     *)
(*   input   T (1 <= T <= 1000), then T lines  a n b m  with           *)
(*           1 <= n, m <= 10^9, 0 <= a < n, 0 <= b < m.                *)
(*   output  per case  "x K"  (K = lcm(n,m), 0 <= x < K), or the line  *)
(*           "no solution".                                            *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted          *)
(* crt verbatim.  This part only reads,    *)
(* converts with Uint63.of_int, calls crt once per case and prints     *)
(* with snd (Uint63.to_int2 _); K <= 10^18 fits a 63-bit word.         *)
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
  let buf = Buffer.create (1 lsl 16) in
  let t = next_int () in
  for _ = 1 to t do
    let a = Uint63.of_int (next_int ()) in
    let n = Uint63.of_int (next_int ()) in
    let b = Uint63.of_int (next_int ()) in
    let m = Uint63.of_int (next_int ()) in
    match crt a n b m with
    | None -> Buffer.add_string buf "no solution\n"
    | Some (x, k) ->
      Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 x)));
      Buffer.add_char buf ' ';
      Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 k)));
      Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
