(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Slow Leak" (open.kattis.com/problems/slowleak).             *)
(*                                                                     *)
(*   input   n m t d; then t repair stations; then m lines "i j k".    *)
(*   output  one line: the minimum distance, or the word "stuck".      *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the array module of the route)   *)
(* and slowleak exactly as `make extract` produced it.    *)
(* This part is the untrusted wrapper: read, convert, call once,       *)
(* print.  It does no arithmetic on the values.  m is read only to     *)
(* size the three road columns; it is not passed to the function.      *)
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
  let m = next_int () in
  let t = next_int () in
  let d = next_int () in
  let st = Array.init t (fun _ -> Uint63.of_int (next_int ())) in
  let ri = Array.make m Uint63.zero in
  let rj = Array.make m Uint63.zero in
  let rk = Array.make m Uint63.zero in
  for e = 0 to m - 1 do
    ri.(e) <- Uint63.of_int (next_int ());
    rj.(e) <- Uint63.of_int (next_int ());
    rk.(e) <- Uint63.of_int (next_int ())
  done;
  let r =
    slowleak (Uint63.of_int n) (Uint63.of_int d)
      (Arr.of_array st Uint63.zero)
      (Arr.of_array ri Uint63.zero)
      (Arr.of_array rj Uint63.zero)
      (Arr.of_array rk Uint63.zero)
  in
  (match r with
   | None -> print_string "stuck"
   | Some x -> print_string (string_of_int (snd (Uint63.to_int2 x))));
  print_char '\n'
