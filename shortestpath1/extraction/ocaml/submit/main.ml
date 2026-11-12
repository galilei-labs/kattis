(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Single source shortest path, non-negative weights"          *)
(* (open.kattis.com/problems/shortestpath1).                           *)
(*                                                                     *)
(*   input   test cases "n m q s", m lines "u v w", q query lines,     *)
(*           until the line "0 0 0 0".                                 *)
(*   output  per query the distance or "Impossible"; a blank line      *)
(*           between test cases, as the sample does.                   *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and Shortestpath1Impl as   *)
(* `make extract` produced it (marray route).  This part is the        *)
(* untrusted wrapper: read, convert, call dijkstra once per test case, *)
(* index the queries into its answer, print.  Stdin is read in one go  *)
(* and scanned by hand; output goes through a Buffer.                  *)
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
  let out = Buffer.create (1 lsl 16) in
  let first = ref true in
  let continue = ref true in
  while !continue do
    let n = next_int () in
    let m = next_int () in
    let q = next_int () in
    let s = next_int () in
    if (n = 0 && m = 0 && q = 0 && s = 0) || !pos >= len then
      continue := false
    else begin
      let us = Array.make m Uint63.zero in
      let vs = Array.make m Uint63.zero in
      let ws = Array.make m Uint63.zero in
      for i = 0 to m - 1 do
        us.(i) <- Uint63.of_int (next_int ());
        vs.(i) <- Uint63.of_int (next_int ());
        ws.(i) <- Uint63.of_int (next_int ())
      done;
      let d =
        dijkstra (Uint63.of_int n)
          (Arr.of_array us Uint63.zero)
          (Arr.of_array vs Uint63.zero)
          (Arr.of_array ws Uint63.zero)
          (Uint63.of_int s)
      in
      if not !first then Buffer.add_char out '\n';
      first := false;
      for _ = 1 to q do
        let t = next_int () in
        (match Arr.get d (Uint63.of_int t) with
         | Some x -> Buffer.add_string out (string_of_int (snd (Uint63.to_int2 x)))
         | None -> Buffer.add_string out "Impossible");
        Buffer.add_char out '\n'
      done
    end
  done;
  print_string (Buffer.contents out)
