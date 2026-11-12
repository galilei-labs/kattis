
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Largest Triangle" (open.kattis.com/problems/largesttriangle)*)
(*                                                                     *)
(*   input   N (3 <= N <= 5000), then N lines "x y",                   *)
(*           0 <= x, y <= 4*10^7.                                      *)
(*   output  one line: the largest triangle area, absolute error       *)
(*           at most 1e-5.                                             *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted code.    *)
(* This part is the untrusted wrapper: read, convert, call once,       *)
(* print.  The area is a half-integer below 8*10^14, exact in a        *)
(* double, so "%.6f" prints it exactly.                                *)
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
  let xs = Array.make (max n 0) Uint63.zero in
  let ys = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    xs.(i) <- Uint63.of_int (next_int ());
    ys.(i) <- Uint63.of_int (next_int ())
  done;
  let x = Arr.of_array xs Uint63.zero in
  let y = Arr.of_array ys Uint63.zero in
  let r = largest_triangle x y in
  Printf.printf "%.6f\n" (Float64.to_float r)
