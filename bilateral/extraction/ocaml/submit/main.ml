
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Bilateral Projects" (open.kattis.com/problems/bilateral).   *)
(*                                                                     *)
(*   input   m (1 <= m <= 10 000), then m lines "i j": Stockholm ID i  *)
(*           in [1000, 1999], London ID j in [2000, 2999].             *)
(*   output  k, then k lines, one invited ID each: a smallest vertex   *)
(*           cover, containing 1009 whenever some smallest one does.   *)
(*                                                                     *)
(* Everything above comes from the pipeline (tools/kattis_shim.ml and  *)
(* bilateral exactly as `make extract` produced it).     *)
(* This part is the untrusted wrapper: read, convert, call once, print.*)
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
  let m = next_int () in
  let st = Array.make m Uint63.zero in
  let lo = Array.make m Uint63.zero in
  for k = 0 to m - 1 do
    st.(k) <- Uint63.of_int (next_int ());
    lo.(k) <- Uint63.of_int (next_int ())
  done;
  let x = Arr.of_array st Uint63.zero in
  let y = Arr.of_array lo Uint63.zero in
  let c = bilateral x y in
  let n = Arr.length_to_int (Arr.length c) in
  let b = Buffer.create (8 * (n + 1)) in
  Buffer.add_string b (string_of_int n);
  Buffer.add_char b '\n';
  for k = 0 to n - 1 do
    Buffer.add_string b (string_of_int (snd (Uint63.to_int2 (Arr.get c (Uint63.of_int k)))));
    Buffer.add_char b '\n'
  done;
  print_string (Buffer.contents b)
