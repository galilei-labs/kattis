
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Farming Mars" (open.kattis.com/problems/farmingmars).       *)
(*                                                                     *)
(*   input   n m, then n pH values (reals, six decimals), then m lines *)
(*           "l r" (1 <= l <= r <= n).                                 *)
(*   output  one line per query: "usable" if some pH value is shared   *)
(*           by a strict majority of acres l..r, else "unusable".      *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim and     *)
(* FarmingmarsImpl as `make extract` produced it).  This part is the   *)
(* untrusted wrapper: read, convert, call once, print.  pH values go   *)
(* in through float_of_string then Float64.of_float; equal decimal     *)
(* texts give equal floats.  The whole of stdin is read in one go and  *)
(* scanned by hand.                                                    *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_tok c = c <> ' ' && c <> '\n' && c <> '\r' && c <> '\t' in
  let next_tok () =
    while !pos < len && not (is_tok (String.unsafe_get data !pos)) do
      incr pos
    done;
    let st = !pos in
    while !pos < len && is_tok (String.unsafe_get data !pos) do
      incr pos
    done;
    String.sub data st (!pos - st)
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
  let n = next_int () in
  let m = next_int () in
  let ph = Array.make n (Float64.of_float 0.0) in
  for i = 0 to n - 1 do
    ph.(i) <- Float64.of_float (float_of_string (next_tok ()))
  done;
  let ls = Array.make m Uint63.zero in
  let rs = Array.make m Uint63.zero in
  for j = 0 to m - 1 do
    ls.(j) <- Uint63.of_int (next_int ());
    rs.(j) <- Uint63.of_int (next_int ())
  done;
  let o =
    farmingmars
      (Arr.of_array ph (Float64.of_float 0.0))
      (Arr.of_array ls Uint63.zero)
      (Arr.of_array rs Uint63.zero)
  in
  let buf = Buffer.create (m * 9) in
  for j = 0 to m - 1 do
    Buffer.add_string buf
      (if Arr.get o (Uint63.of_int j) then "usable\n" else "unusable\n")
  done;
  print_string (Buffer.contents buf)
