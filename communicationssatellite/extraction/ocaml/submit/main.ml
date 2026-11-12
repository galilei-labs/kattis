
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Communications Satellite"                                   *)
(* (open.kattis.com/problems/communicationssatellite).                 *)
(*                                                                     *)
(*   input   n (1 <= n <= 2000), then n lines X Y R with               *)
(*           -1000 <= X, Y <= 1000 and 1 <= R <= 100.                  *)
(*   output  the minimal total beam length, abs/rel error < 1e-6.      *)
(*                                                                     *)
(* The shim and the extracted code (marray route) come first; this     *)
(* part only reads, converts, calls once and prints.  Negative X, Y go *)
(* through Uint63.of_int (identity on OCaml's int) onto the word whose *)
(* signed reading is that number.  The float result is printed with    *)
(* 10 decimals.                                                        *)
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
      c <> '-' && (c < '0' || c > '9')
    do
      incr pos
    done;
    let neg = !pos < len && String.unsafe_get data !pos = '-' in
    if neg then incr pos;
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
    if neg then - !v else !v
  in
  let n = next_int () in
  let n = max n 0 in
  let xs = Array.make n Uint63.zero in
  let ys = Array.make n Uint63.zero in
  let rs = Array.make n Uint63.zero in
  for i = 0 to n - 1 do
    xs.(i) <- Uint63.of_int (next_int ());
    ys.(i) <- Uint63.of_int (next_int ());
    rs.(i) <- Uint63.of_int (next_int ())
  done;
  let x = Arr.of_array xs Uint63.zero in
  let y = Arr.of_array ys Uint63.zero in
  let r = Arr.of_array rs Uint63.zero in
  let v = communicationssatellite x y r in
  Printf.printf "%.10f\n" (Float64.to_float v)
