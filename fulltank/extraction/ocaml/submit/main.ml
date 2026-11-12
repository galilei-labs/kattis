
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Full Tank?" (open.kattis.com/problems/fulltank).            *)
(*                                                                     *)
(*   input   n m; n prices; m lines u v d; q; q lines c s e.           *)
(*   output  one line per query: the cheapest price, or "impossible".  *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (the shim and *)
(* the extracted code of the route; [Arr] names the array module).    *)
(* This part is the untrusted wrapper: read, convert into the parallel *)
(* arrays of the spec, call once, print.  It does no arithmetic on the *)
(* values.  None is printed as "impossible".                           *)
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
  let p = Array.init n (fun _ -> Uint63.of_int (next_int ())) in
  let u = Array.make m Uint63.zero in
  let v = Array.make m Uint63.zero in
  let d = Array.make m Uint63.zero in
  for j = 0 to m - 1 do
    u.(j) <- Uint63.of_int (next_int ());
    v.(j) <- Uint63.of_int (next_int ());
    d.(j) <- Uint63.of_int (next_int ())
  done;
  let q = next_int () in
  let c = Array.make q Uint63.zero in
  let s = Array.make q Uint63.zero in
  let e = Array.make q Uint63.zero in
  for i = 0 to q - 1 do
    c.(i) <- Uint63.of_int (next_int ());
    s.(i) <- Uint63.of_int (next_int ());
    e.(i) <- Uint63.of_int (next_int ())
  done;
  let arr a = Arr.of_array a Uint63.zero in
  let o =
    fulltank (Uint63.of_int n) (arr p) (arr u) (arr v) (arr d)
      (arr c) (arr s) (arr e)
  in
  let buf = Buffer.create 4096 in
  for i = 0 to Arr.length_to_int (Arr.length o) - 1 do
    (match Arr.get o (Uint63.of_int i) with
     | Some k -> Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 k)))
     | None -> Buffer.add_string buf "impossible");
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
