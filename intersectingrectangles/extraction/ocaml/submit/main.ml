(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Intersecting Rectangles"                                    *)
(* (open.kattis.com/problems/intersectingrectangles).                  *)
(*                                                                     *)
(*   input   n (1 <= n <= 1e5), then n lines x1 y1 x2 y2, each in      *)
(*           [-1e9, 1e9], x1 < x2, y1 < y2, all x and all y distinct.  *)
(*   output  one line: 1 if some pair of boundaries meet, else 0.      *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the marray extraction  *)
(* verbatim.  This part is the untrusted wrapper: read the whole of    *)
(* stdin, scan by hand, split the four coordinate columns, convert     *)
(* (Uint63.of_int lands a negative on the word whose signed reading is *)
(* that number), call once per test case, print.  "Each test case"     *)
(* in the statement: test cases are read until the input runs out.     *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let skip () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c <> '-' && (c < '0' || c > '9')
    do
      incr pos
    done
  in
  let next_int () =
    skip ();
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
  let buf = Buffer.create 16 in
  skip ();
  while !pos < len do
    let n = next_int () in
    let x1 = Array.make (max n 0) Uint63.zero in
    let y1 = Array.make (max n 0) Uint63.zero in
    let x2 = Array.make (max n 0) Uint63.zero in
    let y2 = Array.make (max n 0) Uint63.zero in
    for i = 0 to n - 1 do
      x1.(i) <- Uint63.of_int (next_int ());
      y1.(i) <- Uint63.of_int (next_int ());
      x2.(i) <- Uint63.of_int (next_int ());
      y2.(i) <- Uint63.of_int (next_int ())
    done;
    let conv a = Arr.of_array a Uint63.zero in
    let b =
      intersecting_rectangles
        (conv x1) (conv y1) (conv x2) (conv y2)
    in
    Buffer.add_string buf (if b then "1\n" else "0\n");
    skip ()
  done;
  print_string (Buffer.contents buf)
