
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Indoorienteering" (open.kattis.com/problems/indoorienteering).*)
(*                                                                     *)
(*   input   n L (2 <= n <= 14, 1 <= L <= 10^15), then the n x n       *)
(*           distance matrix, row by row.                              *)
(*   output  one line: "possible" or "impossible".                     *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (the shim,    *)
(* then IndoorienteeringImpl as `make extract` produced it).  This     *)
(* part is the untrusted wrapper: read, convert, call once, print.     *)
(* All values are nonnegative and below 2^62, so Uint63.of_int is the  *)
(* identity on them.                                                   *)
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
  let l = next_int () in
  let rows =
    Array.init n (fun _ ->
        let r = Array.init n (fun _ -> Uint63.of_int (next_int ())) in
        Arr.of_array r Uint63.zero)
  in
  let d = Arr.of_array rows (Arr.of_array [||] Uint63.zero) in
  let b = indoorienteering d (Uint63.of_int l) in
  print_string (if b then "possible" else "impossible");
  print_char '\n'
