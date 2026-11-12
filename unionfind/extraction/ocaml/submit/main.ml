
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Union-Find" (open.kattis.com/problems/unionfind).           *)
(*                                                                     *)
(*   input   N Q, then Q lines "= a b" (union) or "? a b" (query),     *)
(*           0 <= a, b < N <= 10^6, Q <= 10^6.                         *)
(*   output  one line "yes" / "no" per query, in order.                *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the marray extraction  *)
(* of UnionfindImpl verbatim.  This part is the untrusted wrapper:     *)
(* read all of stdin, scan by hand, build the three operation columns, *)
(* call run_ops once, print the answers at the query positions only    *)
(* (the union positions of the result are unspecified).               *)
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
  (* the next '=' or '?' *)
  let next_op () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c <> '=' && c <> '?'
    do
      incr pos
    done;
    let c = String.unsafe_get data !pos in
    incr pos;
    c = '='
  in
  let n = next_int () in
  let q = next_int () in
  let u = Array.make q false in
  let a = Array.make q Uint63.zero in
  let b = Array.make q Uint63.zero in
  for i = 0 to q - 1 do
    u.(i) <- next_op ();
    a.(i) <- Uint63.of_int (next_int ());
    b.(i) <- Uint63.of_int (next_int ())
  done;
  let out =
    run_ops (Uint63.of_int n)
      (Arr.of_array u false)
      (Arr.of_array a Uint63.zero)
      (Arr.of_array b Uint63.zero)
  in
  let buf = Buffer.create (4 * q + 16) in
  for i = 0 to q - 1 do
    if not u.(i) then
      Buffer.add_string buf
        (if Arr.get out (Uint63.of_int i) then "yes\n" else "no\n")
  done;
  print_string (Buffer.contents buf)
