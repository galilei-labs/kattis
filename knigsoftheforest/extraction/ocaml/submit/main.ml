
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Knigs of the Forest" (open.kattis.com/problems/            *)
(* knigsoftheforest).                                                  *)
(*                                                                     *)
(*   input   k n; then Karl-Algtav's "y p"; then n + k - 2 lines "y p" *)
(*           for the other moose.                                      *)
(*   output  the year Karl-Algtav wins, or "unknown".                  *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim and     *)
(* KnigsoftheforestImpl as `make extract` produced it).  This part is  *)
(* the untrusted wrapper: read, convert, call once, print.  The other  *)
(* moose's years and strengths go in as two parallel arrays, in input  *)
(* order, as the spec's ys and ps.                                     *)
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
  let k = next_int () in
  let n = next_int () in
  let y = next_int () in
  let p = next_int () in
  let m = max (n + k - 2) 0 in
  let ys = Array.make m Uint63.zero in
  let ps = Array.make m Uint63.zero in
  for i = 0 to m - 1 do
    ys.(i) <- Uint63.of_int (next_int ());
    ps.(i) <- Uint63.of_int (next_int ())
  done;
  let ya = Arr.of_array ys Uint63.zero in
  let pa = Arr.of_array ps Uint63.zero in
  (match
     knigsoftheforest (Uint63.of_int k) (Uint63.of_int n)
       (Uint63.of_int y) (Uint63.of_int p) ya pa
   with
   | Some w -> print_string (string_of_int (snd (Uint63.to_int2 w)))
   | None -> print_string "unknown");
  print_char '\n'
