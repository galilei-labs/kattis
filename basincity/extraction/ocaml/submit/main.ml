
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Basin City Surveillance" (open.kattis.com/problems/basincity)*)
(*                                                                     *)
(*   input   k (0 <= k <= 15); n (1 <= n <= 100 000); then n lines     *)
(*           "d v_1 .. v_d" (0 <= d <= 4), neighbours numbered 1..n.   *)
(*   output  "possible" or "impossible".                               *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted code     *)
(* (marray route, [Arr] = Marray).  This part is the untrusted         *)
(* wrapper: read, convert, call once, print.  Row x-1 of the array     *)
(* holds the 1-based neighbour numbers of intersection x, verbatim, as *)
(* the spec's repr on array (array uint) demands.                      *)
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
  let empty = Arr.of_array [||] Uint63.zero in
  let rows = Array.make n empty in
  for i = 0 to n - 1 do
    let d = next_int () in
    let r = Array.make d Uint63.zero in
    for j = 0 to d - 1 do
      r.(j) <- Uint63.of_int (next_int ())
    done;
    rows.(i) <- Arr.of_array r Uint63.zero
  done;
  let adj = Arr.of_array rows empty in
  print_string
    (if basincity (Uint63.of_int k) adj then "possible\n"
     else "impossible\n")
