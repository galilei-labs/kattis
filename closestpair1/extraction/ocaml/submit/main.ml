(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Closest Pair (Uniform)" (open.kattis.com/problems/          *)
(* closestpair1).                                                      *)
(*                                                                     *)
(*   input   several test cases: n (2 <= n <= 100 000), then n lines  *)
(*           "x y" (floats, at most 2 decimals, |.| <= 100 000);       *)
(*           terminated by a case beginning with 0.                    *)
(*   output  per case, one line "x1 y1 x2 y2": any closest pair.       *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* closestpair exactly as `make extract` produced it, *)
(* marray route).  This part is the untrusted wrapper: read, convert   *)
(* with Float64.of_float, call once per case, print.  It does no       *)
(* arithmetic on the values: the two points are printed as the input's *)
(* own tokens, verbatim, at the indices the verified code returned     *)
(* (read back with [snd (Uint63.to_int2 _)]).                          *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* The next whitespace-separated token, as (start, length). *)
  let next_tok () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c = ' ' || c = '\n' || c = '\r' || c = '\t'
    do
      incr pos
    done;
    let s = !pos in
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      not (c = ' ' || c = '\n' || c = '\r' || c = '\t')
    do
      incr pos
    done;
    (s, !pos - s)
  in
  let out = Buffer.create (1 lsl 16) in
  let rec cases () =
    let (s, l) = next_tok () in
    if l > 0 then begin
      let n = int_of_string (String.sub data s l) in
      if n > 0 then begin
        let xt = Array.make n "" and yt = Array.make n "" in
        let xs = Array.make n (Float64.of_float 0.0) and ys = Array.make n (Float64.of_float 0.0) in
        for k = 0 to n - 1 do
          let (s, l) = next_tok () in
          let t = String.sub data s l in
          xt.(k) <- t;
          xs.(k) <- Float64.of_float (float_of_string t);
          let (s, l) = next_tok () in
          let t = String.sub data s l in
          yt.(k) <- t;
          ys.(k) <- Float64.of_float (float_of_string t)
        done;
        (* Arr.of_array copies; the implem never writes its inputs. *)
        let x = Arr.of_array xs (Float64.of_float 0.0) in
        let y = Arr.of_array ys (Float64.of_float 0.0) in
        let (i, j) = closestpair x y in
        let i = snd (Uint63.to_int2 i) and j = snd (Uint63.to_int2 j) in
        Buffer.add_string out xt.(i); Buffer.add_char out ' ';
        Buffer.add_string out yt.(i); Buffer.add_char out ' ';
        Buffer.add_string out xt.(j); Buffer.add_char out ' ';
        Buffer.add_string out yt.(j); Buffer.add_char out '\n';
        cases ()
      end
    end
  in
  cases ();
  print_string (Buffer.contents out)
