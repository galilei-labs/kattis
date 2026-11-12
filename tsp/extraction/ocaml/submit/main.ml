
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Travelling Salesperson 2D" (open.kattis.com/problems/tsp).  *)
(*                                                                     *)
(*   input   N (1 <= N <= 1000), then N lines "x y" of reals,          *)
(*           |x|, |y| <= 10^6.                                         *)
(*   output  N lines, the 0-based index of the i-th point visited.     *)
(*                                                                     *)
(* Scored problem: any tour is accepted and scored by its length.      *)
(* Everything above this comment comes from the pipeline (shim,        *)
(* Bigint, TspImpl as extracted on the arrays_bigint route, Arr =      *)
(* Marray_raw).  This part is the untrusted wrapper: read the whole of *)
(* stdin, split on whitespace, float_of_string each coordinate, wrap   *)
(* with Float64.of_float, call tsp once, print the indices     *)
(* read back with [snd (Uint63.to_int2 _)].                            *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_tok () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let s = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do incr pos done;
    String.sub data s (!pos - s)
  in
  let n = int_of_string (next_tok ()) in
  let xs = Array.make n (Float64.of_float 0.0) in
  let ys = Array.make n (Float64.of_float 0.0) in
  for i = 0 to n - 1 do
    xs.(i) <- Float64.of_float (float_of_string (next_tok ()));
    ys.(i) <- Float64.of_float (float_of_string (next_tok ()))
  done;
  let x = Arr.of_array xs (Float64.of_float 0.0) in
  let y = Arr.of_array ys (Float64.of_float 0.0) in
  let t = tsp x y in
  let m = Arr.length_to_int (Arr.length t) in
  let b = Buffer.create (m * 5) in
  for i = 0 to m - 1 do
    Buffer.add_string b (string_of_int (snd (Uint63.to_int2 (Arr.get t (Uint63.of_int i)))));
    Buffer.add_char b '\n'
  done;
  print_string (Buffer.contents b)
