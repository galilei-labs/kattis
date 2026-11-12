
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "YATP" (open.kattis.com/problems/yatp).                      *)
(*                                                                     *)
(*   input   n (1 <= n <= 200 000); n penalties p (1..10^6); n-1 lines *)
(*           "i j w" (1-based nodes, 1 <= w <= 10^6).                  *)
(*   output  one integer: the sum over nodes of the cheapest path      *)
(*           starting there (at most n * 10^12 <= 2*10^17, one word).  *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml and yatp as `make extract`     *)
(* produced it (marray route).  This part reads stdin at once, scans   *)
(* by hand, builds the four columns p, eu, ev, ew, calls once, prints. *)
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
  let n = next_int () in
  let m = max (n - 1) 0 in
  let p = Array.make n Uint63.zero in
  for i = 0 to n - 1 do
    p.(i) <- Uint63.of_int (next_int ())
  done;
  let eu = Array.make m Uint63.zero in
  let ev = Array.make m Uint63.zero in
  let ew = Array.make m Uint63.zero in
  for k = 0 to m - 1 do
    eu.(k) <- Uint63.of_int (next_int ());
    ev.(k) <- Uint63.of_int (next_int ());
    ew.(k) <- Uint63.of_int (next_int ())
  done;
  let s =
    yatp
      (Arr.of_array p Uint63.zero)
      (Arr.of_array eu Uint63.zero)
      (Arr.of_array ev Uint63.zero)
      (Arr.of_array ew Uint63.zero)
  in
  print_string (string_of_int (snd (Uint63.to_int2 s)));
  print_char '\n'
