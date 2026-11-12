
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Security Badge" (open.kattis.com/problems/securitybadge).   *)
(*                                                                     *)
(*   input   N L B, then S D, then L lines "a b x y" (a lock from room *)
(*           a to room b for badges x .. y).                           *)
(*   output  one line: the number of badges in 1 .. B getting from S   *)
(*           to D.                                                     *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* SecuritybadgeImpl as `make extract` produced it, then Arr).  This   *)
(* part is the untrusted wrapper: read, convert, call once, print.     *)
(* The entry point takes n b s d, then the four lock columns a b x y,  *)
(* all 1-based as in the input.  All values are non-negative.          *)
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
  let l = next_int () in
  let b = next_int () in
  let s = next_int () in
  let d = next_int () in
  let la = Array.make l Uint63.zero in
  let lb = Array.make l Uint63.zero in
  let lx = Array.make l Uint63.zero in
  let ly = Array.make l Uint63.zero in
  for i = 0 to l - 1 do
    la.(i) <- Uint63.of_int (next_int ());
    lb.(i) <- Uint63.of_int (next_int ());
    lx.(i) <- Uint63.of_int (next_int ());
    ly.(i) <- Uint63.of_int (next_int ())
  done;
  let conv a = Arr.of_array a Uint63.zero in
  let o =
    securitybadge (Uint63.of_int n) (Uint63.of_int b)
      (Uint63.of_int s) (Uint63.of_int d) (conv la) (conv lb) (conv lx)
      (conv ly)
  in
  print_string (string_of_int (snd (Uint63.to_int2 o)));
  print_char '\n'
