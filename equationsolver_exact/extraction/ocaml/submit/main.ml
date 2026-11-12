
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Linear Equation Solver" (problem id: equationsolver).       *)
(*                                                                     *)
(*   input   several cases: n (1 <= n <= 100), n rows of n floats      *)
(*           (the matrix A), one row of n floats (b); ended by n = 0.  *)
(*   output  per case: the n entries of x separated by spaces          *)
(*           (error <= 1e-3 allowed), or "multiple", or "inconsistent".*)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml), tools/bigint.ml and the extracted code of   *)
(* the arrays_bigint route ([Arr] = Marray_raw).  This part is the     *)
(* untrusted wrapper: read, convert, call solve once per case, print.  *)
(* It does no arithmetic on the values.  Tokens are split on           *)
(* whitespace and read with float_of_string (the binary64 the input    *)
(* text denotes, as the spec's repr_float); entries print with %.15g.  *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_tok () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let s = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do incr pos done;
    String.sub data s (!pos - s)
  in
  let buf = Buffer.create 65536 in
  let rec cases () =
    let t = next_tok () in
    if t <> "" then begin
      let n = int_of_string t in
      if n > 0 then begin
        let fz = Float64.of_float 0.0 in
        let row () =
          Arr.of_array (Array.init n (fun _ -> Float64.of_float (float_of_string (next_tok ())))) fz
        in
        let rows = Array.init n (fun _ -> row ()) in
        let a = Arr.of_array rows (Arr.of_array [||] fz) in
        let b = row () in
        (match solve (Uint63.of_int n) a b with
         | Unique x ->
           for i = 0 to n - 1 do
             if i > 0 then Buffer.add_char buf ' ';
             Buffer.add_string buf
               (Printf.sprintf "%.15g" (Float64.to_float (Arr.get x (Uint63.of_int i))))
           done;
           Buffer.add_char buf '\n'
         | Multiple -> Buffer.add_string buf "multiple\n"
         | Inconsistent -> Buffer.add_string buf "inconsistent\n");
        cases ()
      end
    end
  in
  cases ();
  print_string (Buffer.contents buf)
