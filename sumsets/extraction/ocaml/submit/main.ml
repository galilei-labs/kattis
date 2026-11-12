(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Sumsets" (open.kattis.com/problems/sumsets).                *)
(*                                                                     *)
(*   input   N (1 <= N <= 4000), then N distinct integers, one per     *)
(*           line, each in [-536 870 912, 536 870 911].                *)
(*   output  one line: the largest d = a + b + c (a, b, c, d distinct  *)
(*           elements), or "no solution".                              *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and SumsetsImpl as `make   *)
(* extract` produced it (marray route).  This part is the untrusted    *)
(* wrapper: read, convert, call once, print; no arithmetic on values.  *)
(* Negatives go in through Uint63.of_int and the answer comes back     *)
(* with [snd (Uint63.to_int2 _)] (signed reading).                     *)
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
  let cells = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  let a = Arr.of_array cells Uint63.zero in
  (match sumsets a with
   | Some d -> print_string (string_of_int (snd (Uint63.to_int2 d)))
   | None -> print_string "no solution");
  print_char '\n'
