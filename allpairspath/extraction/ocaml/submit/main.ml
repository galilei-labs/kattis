(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "All Pairs Shortest Path" (open.kattis.com/problems/          *)
(* allpairspath).                                                      *)
(*                                                                     *)
(*   input   test cases "n m q", m edges "u v w", q queries "u v",     *)
(*           terminated by "0 0 0".                                    *)
(*   output  per query: the distance, "Impossible" or "-Infinity";     *)
(*           a blank line between test cases (the statement says       *)
(*           after each; the sample .ans has no final blank line and   *)
(*           Kattis's default checker ignores whitespace).             *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted code     *)
(* verbatim.  This part is the untrusted wrapper: read, convert, call  *)
(* allpairspath once per test case, answer the queries from the        *)
(* returned n x n matrix.  It does no arithmetic on the values.        *)
(* Weights may be negative: Uint63.of_int lands on the word whose      *)
(* signed reading is the weight; distances are read back with          *)
(* [snd (Uint63.to_int2 _)].                                           *)
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
  let buf = Buffer.create (1 lsl 16) in
  let first = ref true in
  let rec loop () =
    if !pos < len then begin
      let n = next_int () in
      let m = next_int () in
      let q = next_int () in
      if not (n = 0 && m = 0 && q = 0) then begin
        let us = Array.make m Uint63.zero in
        let vs = Array.make m Uint63.zero in
        let ws = Array.make m Uint63.zero in
        for k = 0 to m - 1 do
          us.(k) <- Uint63.of_int (next_int ());
          vs.(k) <- Uint63.of_int (next_int ());
          ws.(k) <- Uint63.of_int (next_int ())
        done;
        let res =
          allpairspath (Uint63.of_int n)
            (Arr.of_array us Uint63.zero)
            (Arr.of_array vs Uint63.zero)
            (Arr.of_array ws Uint63.zero)
        in
        if not !first then Buffer.add_char buf '\n';
        first := false;
        for _ = 1 to q do
          let u = next_int () in
          let v = next_int () in
          let row = Arr.get res (Uint63.of_int u) in
          (match Arr.get row (Uint63.of_int v) with
           | Impossible -> Buffer.add_string buf "Impossible"
           | NegInfinity -> Buffer.add_string buf "-Infinity"
           | Distance d ->
             Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 d))));
          Buffer.add_char buf '\n'
        done;
        loop ()
      end
    end
  in
  loop ();
  print_string (Buffer.contents buf)
