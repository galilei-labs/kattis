(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Plotting Polynomials" (open.kattis.com/problems/plot).      *)
(*                                                                     *)
(*   input   one line: n (1 <= n <= 6), then the n+1 coefficients      *)
(*           a_n .. a_1 a_0 (|a_i| <= 50, a_n <> 0).                   *)
(*   output  one line: C_0 C_1 .. C_n separated by spaces.             *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and plot as       *)
(* `make extract` produced it.  This part is the untrusted wrapper:    *)
(* read, convert, call once, print.  It does no arithmetic on values.  *)
(* Negative coefficients go in through Uint63.of_int; the constants    *)
(* (possibly negative) come back with [snd (Uint63.to_int2 _)].        *)
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
  let k = max (n + 1) 0 in
  let cells = Array.make k Uint63.zero in
  for i = 0 to k - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  let a = Arr.of_array cells Uint63.zero in
  let c = plot (Uint63.of_int n) a in
  let m = Arr.length_to_int (Arr.length c) in
  let buf = Buffer.create 64 in
  for i = 0 to m - 1 do
    if i > 0 then Buffer.add_char buf ' ';
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get c (Uint63.of_int i)))))
  done;
  Buffer.add_char buf '\n';
  print_string (Buffer.contents buf)
