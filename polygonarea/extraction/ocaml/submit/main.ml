(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Polygon Area" (open.kattis.com/problems/polygonarea).       *)
(*                                                                     *)
(*   input   up to 25 cases: n (3 <= n <= 1000), then n lines x y      *)
(*           (|x|, |y| <= 10 000); terminated by a case n = 0.         *)
(*   output  per case one line  D A : D = CCW / CW, A the area with    *)
(*           exactly one decimal.                                      *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted          *)
(* PolygonareaImpl verbatim.  This part is the untrusted wrapper: it   *)
(* reads, converts, calls signed_area2 once per case (the shoelace     *)
(* sum s, twice the signed area) and prints the sign of s as the       *)
(* direction (s > 0: CCW) and |s| / 2 as the area: |s| div 2, then     *)
(* ".5" when s is odd, ".0" otherwise.                                 *)
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
  let out = Buffer.create 1024 in
  let rec loop () =
    let n = if !pos < len then next_int () else 0 in
    if n > 0 then begin
      let xs = Array.make n Uint63.zero in
      let ys = Array.make n Uint63.zero in
      for i = 0 to n - 1 do
        xs.(i) <- Uint63.of_int (next_int ());
        ys.(i) <- Uint63.of_int (next_int ())
      done;
      let s =
        snd
          (Uint63.to_int2
             (signed_area2
                (Arr.of_array xs Uint63.zero)
                (Arr.of_array ys Uint63.zero)))
      in
      let a = abs s in
      Buffer.add_string out (if s > 0 then "CCW " else "CW ");
      Buffer.add_string out (string_of_int (a / 2));
      Buffer.add_string out (if a land 1 = 1 then ".5\n" else ".0\n");
      loop ()
    end
  in
  loop ();
  print_string (Buffer.contents out)
