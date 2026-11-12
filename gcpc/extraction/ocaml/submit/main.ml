(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Galactic Collegiate Programming Contest" (gcpc).            *)
(*                                                                     *)
(*   input   n m, then m lines "t p" (1 <= n, m <= 10^5,               *)
(*           1 <= t <= n, 1 <= p <= 1000).                             *)
(*   output  m lines: the rank of team 1 after each event.             *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the array module of the route)   *)
(* and gcpc exactly as `make extract` produced it.  This part *)
(* is the untrusted wrapper: read, convert, call once, print.          *)
(* stdin is read in one go and scanned by hand; the m answers go       *)
(* through one Buffer.                                                 *)
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
  let n = next_int () in
  let m = next_int () in
  let ts = Array.make m Uint63.zero in
  let ps = Array.make m Uint63.zero in
  for j = 0 to m - 1 do
    ts.(j) <- Uint63.of_int (next_int ());
    ps.(j) <- Uint63.of_int (next_int ())
  done;
  let xt = Arr.of_array ts Uint63.zero in
  let xp = Arr.of_array ps Uint63.zero in
  let o = gcpc (Uint63.of_int n) xt xp in
  let k = Arr.length_to_int (Arr.length o) in
  let buf = Buffer.create (k * 7) in
  for i = 0 to k - 1 do
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get o (Uint63.of_int i)))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
