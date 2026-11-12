(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Interval Cover" (open.kattis.com/problems/intervalcover).   *)
(*                                                                     *)
(*   input   up to 30 test cases until end of file: A B, then n, then  *)
(*           n lines a_i b_i (reals, at most 6 decimals).              *)
(*   output  per case: the count, then a line of the indices of one    *)
(*           minimal cover (any order), or the line "impossible".      *)
(*                                                                     *)
(* The shim and cover above come from the pipeline;  *)
(* this part reads, converts (float_of_string, then Float64.of_float), *)
(* calls once per case and prints.  It does no arithmetic on the       *)
(* values.  Several minimal covers may exist: submit/check verifies    *)
(* the property rather than the bytes.                                 *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let skip () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done
  in
  let token () =
    skip ();
    let s = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data s (!pos - s)
  in
  let next_float () = Float64.of_float (float_of_string (token ())) in
  let next_int () = int_of_string (token ()) in
  let out = Buffer.create (1 lsl 16) in
  skip ();
  while !pos < len do
    let a = next_float () in
    let b = next_float () in
    let n = next_int () in
    let ls = Array.make n (Float64.of_float 0.) in
    let rs = Array.make n (Float64.of_float 0.) in
    for i = 0 to n - 1 do
      ls.(i) <- next_float ();
      rs.(i) <- next_float ()
    done;
    let zero = Float64.of_float 0. in
    (match
       cover a b (Arr.of_array ls zero) (Arr.of_array rs zero)
     with
     | None -> Buffer.add_string out "impossible\n"
     | Some t ->
       let k = Arr.length_to_int (Arr.length t) in
       Buffer.add_string out (string_of_int k);
       Buffer.add_char out '\n';
       for j = 0 to k - 1 do
         if j > 0 then Buffer.add_char out ' ';
         Buffer.add_string out
           (string_of_int (snd (Uint63.to_int2 (Arr.get t (Uint63.of_int j)))))
       done;
       Buffer.add_char out '\n');
    skip ()
  done;
  print_string (Buffer.contents out)
