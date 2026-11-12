
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Timing" (open.kattis.com/problems/timing).                  *)
(*                                                                     *)
(*   input   T test cases; each: N l t, then N doubles u_i, then l     *)
(*           lines "s_j t_j p_j".                                      *)
(*   output  per test case, the lowest indicator (abs/rel error 1e-6). *)
(*                                                                     *)
(* Route arrays_bigint (Arr = Marray_raw): plain OCaml arrays.  This   *)
(* part is the untrusted wrapper: read, convert, call once per test    *)
(* case, print.  It does no arithmetic on the values.                  *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_tok () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let st = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do incr pos done;
    String.sub data st (!pos - st)
  in
  let next_int () = int_of_string (next_tok ()) in
  let next_float () = Float64.of_float (float_of_string (next_tok ())) in
  let buf = Buffer.create 256 in
  let cases = next_int () in
  for _ = 1 to cases do
    let n = next_int () in
    let l = next_int () in
    let t = next_int () in
    let u = Array.init n (fun _ -> next_float ()) in
    let src = Array.make l Uint63.zero in
    let dst = Array.make l Uint63.zero in
    let frac = Array.make l (Float64.of_float 0.) in
    for j = 0 to l - 1 do
      src.(j) <- Uint63.of_int (next_int ());
      dst.(j) <- Uint63.of_int (next_int ());
      frac.(j) <- next_float ()
    done;
    let z = Float64.of_float 0. in
    let out =
      timing (Uint63.of_int t) (Arr.of_array u z)
        (Arr.of_array src Uint63.zero) (Arr.of_array dst Uint63.zero)
        (Arr.of_array frac z)
    in
    Buffer.add_string buf (Printf.sprintf "%.9f\n" (Float64.to_float out))
  done;
  print_string (Buffer.contents buf)
