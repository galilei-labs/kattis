
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Polynomial Multiplication 1" (open.kattis.com/problems/     *)
(* polymul1).                                                          *)
(*                                                                     *)
(*   input   T (<= 100), then per case: n1, the n1+1 coefficients      *)
(*           a_0 .. a_n1, n2, the n2+1 coefficients b_0 .. b_n2        *)
(*           (1 <= n <= 255, signed 32-bit coefficients).              *)
(*   output  per case: the product's degree on one line, then its      *)
(*           coefficients, lowest degree first, on one line.           *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the array module of the route)   *)
(* and polymul exactly as `make extract` produced it.     *)
(* This part is the untrusted wrapper: read, convert, call once per    *)
(* case, print.  It does no arithmetic on the values.  The spec fixes  *)
(* the result's length to len a + len b - 1, so the degree printed is  *)
(* that length minus one, as in the sample.  Negative numbers go in    *)
(* through Uint63.of_int and come back with [snd (Uint63.to_int2 _)].  *)
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
  let read_poly () =
    let n = next_int () in
    let cells = Array.make (n + 1) Uint63.zero in
    for i = 0 to n do
      cells.(i) <- Uint63.of_int (next_int ())
    done;
    Arr.of_array cells Uint63.zero
  in
  let out = Buffer.create (1 lsl 16) in
  let t = next_int () in
  for _ = 1 to t do
    let a = read_poly () in
    let b = read_poly () in
    let p = polymul a b in
    let m = Arr.length_to_int (Arr.length p) in
    Buffer.add_string out (string_of_int (m - 1));
    Buffer.add_char out '\n';
    for i = 0 to m - 1 do
      if i > 0 then Buffer.add_char out ' ';
      Buffer.add_string out
        (string_of_int (snd (Uint63.to_int2 (Arr.get p (Uint63.of_int i)))))
    done;
    Buffer.add_char out '\n'
  done;
  print_string (Buffer.contents out)
