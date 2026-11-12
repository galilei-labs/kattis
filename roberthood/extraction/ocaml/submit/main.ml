
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Robert Hood" (open.kattis.com/problems/roberthood).         *)
(*                                                                     *)
(*   input   C (2 <= C <= 100 000), then C lines "x y", |x|,|y|<=1000. *)
(*   output  the largest distance between two points, a float; the     *)
(*           judge accepts an absolute or relative error below 1e-6.   *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and RoberthoodImpl exactly *)
(* as `make extract` produced it (marray route).  This part is the     *)
(* untrusted wrapper: read, convert, call once, print.                 *)
(* stdin is read whole and scanned by hand; a negative coordinate goes *)
(* through Uint63.of_int and lands on the word whose signed reading is *)
(* that number.  The answer is printed with "%.9f".                     *)
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
  let xs = Array.make (max n 0) Uint63.zero in
  let ys = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    xs.(i) <- Uint63.of_int (next_int ());
    ys.(i) <- Uint63.of_int (next_int ())
  done;
  let x = Arr.of_array xs Uint63.zero in
  let y = Arr.of_array ys Uint63.zero in
  let d = roberthood x y in
  Printf.printf "%.9f\n" (Float64.to_float d)
