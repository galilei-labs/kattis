
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Worst Weather Ever" (open.kattis.com/problems/worstweather).*)
(*                                                                     *)
(*   input   several cases: n, n lines "y r" (y increasing), m, m lines *)
(*           "Y X" (Y < X); terminated by n = 0, m = 0.                 *)
(*   output  per query true / maybe / false, one per line; a blank     *)
(*           line between two test cases.                              *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml, [Arr] = Marray on this route) and the        *)
(* extracted WorstweatherImpl verbatim.  This part is the untrusted    *)
(* wrapper: read, convert, call once per case, print.  Years may be    *)
(* negative: Uint63.of_int lands on the word whose signed reading is   *)
(* the year.  The call is worstweather ys rs qy qx (the Module Type's  *)
(* order: the earlier year Y first, then X).                           *)
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
    if !pos >= len then 0
    else begin
      let neg = String.unsafe_get data !pos = '-' in
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
    end
  in
  let out = Buffer.create (1 lsl 16) in
  let first = ref true in
  let continue = ref true in
  while !continue do
    let n = next_int () in
    if n <= 0 then continue := false
    else begin
      let ys = Array.make n Uint63.zero and rs = Array.make n Uint63.zero in
      for i = 0 to n - 1 do
        ys.(i) <- Uint63.of_int (next_int ());
        rs.(i) <- Uint63.of_int (next_int ())
      done;
      let m = next_int () in
      let qy = Array.make (max m 0) Uint63.zero
      and qx = Array.make (max m 0) Uint63.zero in
      for k = 0 to m - 1 do
        qy.(k) <- Uint63.of_int (next_int ());
        qx.(k) <- Uint63.of_int (next_int ())
      done;
      let res =
        worstweather
          (Arr.of_array ys Uint63.zero) (Arr.of_array rs Uint63.zero)
          (Arr.of_array qy Uint63.zero) (Arr.of_array qx Uint63.zero)
      in
      if not !first then Buffer.add_char out '\n';
      first := false;
      for k = 0 to m - 1 do
        Buffer.add_string out
          (match Arr.get res (Uint63.of_int k) with
           | Ans_true -> "true\n"
           | Ans_maybe -> "maybe\n"
           | Ans_false -> "false\n")
      done
    end
  done;
  print_string (Buffer.contents out)
