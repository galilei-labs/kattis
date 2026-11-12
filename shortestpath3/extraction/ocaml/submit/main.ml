(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Single source shortest path, negative weights"              *)
(* (shortestpath3).  Several cases, each: n m q s, m lines u v w       *)
(* (w in [-2000, 2000]), q query nodes; ended by "0 0 0 0".  Output:   *)
(* per query the distance, "Impossible" or "-Infinity"; a blank line   *)
(* between cases, as the sample shows.                                 *)
(*                                                                     *)
(* Above this part: tools/kattis_shim.ml and the marray extraction     *)
(* verbatim.  This part is the untrusted wrapper: scan stdin by hand,  *)
(* convert (Uint63.of_int; negative weights land on the word whose     *)
(* signed reading is the weight), call once per case, print the        *)
(* answers (distances read back with snd (Uint63.to_int2 _)).          *)
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
  let buf = Buffer.create (1 lsl 16) in
  let first = ref true in
  let continue = ref true in
  while !continue do
    let n = next_int () in
    let m = next_int () in
    let q = next_int () in
    let s = next_int () in
    if n = 0 && m = 0 && q = 0 && s = 0 then continue := false
    else begin
      let us = Array.make m Uint63.zero in
      let vs = Array.make m Uint63.zero in
      let ws = Array.make m Uint63.zero in
      for j = 0 to m - 1 do
        us.(j) <- Uint63.of_int (next_int ());
        vs.(j) <- Uint63.of_int (next_int ());
        ws.(j) <- Uint63.of_int (next_int ())
      done;
      let qs = Array.make q Uint63.zero in
      for j = 0 to q - 1 do
        qs.(j) <- Uint63.of_int (next_int ())
      done;
      let o =
        shortestpath3 (Uint63.of_int n) (Uint63.of_int s)
          (Arr.of_array us Uint63.zero) (Arr.of_array vs Uint63.zero)
          (Arr.of_array ws Uint63.zero) (Arr.of_array qs Uint63.zero)
      in
      if not !first then Buffer.add_char buf '\n';
      first := false;
      for j = 0 to q - 1 do
        (match Arr.get o (Uint63.of_int j) with
         | Dist d -> Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 d)))
         | Impossible -> Buffer.add_string buf "Impossible"
         | MinusInfinity -> Buffer.add_string buf "-Infinity");
        Buffer.add_char buf '\n'
      done
    end
  done;
  print_string (Buffer.contents buf)
