(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Self Balancing Binary Search Tree" (selfbalancingbst).      *)
(*                                                                     *)
(*   input   q, then q lines "<id> <op> [arg] [arg]".                  *)
(*   output  one line per r / g / z command: the number, or "-" when   *)
(*           the extracted function returns None (cursor unset).       *)
(*                                                                     *)
(* Columns as the spec header says: ids, ops (character code), xs, ys, *)
(* an absent argument as 0.  The arguments of a line are the integers   *)
(* up to its end of line.  Untrusted wrapper: read, convert, call once,*)
(* print.  Negative values go through Uint63.of_int and are read back  *)
(* with [snd (Uint63.to_int2 _)].                                      *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let skip_blank () =
    while !pos < len && (let c = String.unsafe_get data !pos in
                         c = ' ' || c = '\t' || c = '\r') do incr pos done
  in
  let skip_ws () =
    while !pos < len && (let c = String.unsafe_get data !pos in
                         c = ' ' || c = '\t' || c = '\r' || c = '\n') do incr pos done
  in
  let read_int () =
    let neg = !pos < len && String.unsafe_get data !pos = '-' in
    if neg then incr pos;
    let v = ref 0 in
    while !pos < len && (let c = String.unsafe_get data !pos in c >= '0' && c <= '9') do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    if neg then - !v else !v
  in
  (* true when an integer starts at pos on the current line *)
  let int_ahead () =
    skip_blank ();
    !pos < len &&
    (let c = String.unsafe_get data !pos in
     (c >= '0' && c <= '9') ||
     (c = '-' && !pos + 1 < len &&
      let d = String.unsafe_get data (!pos + 1) in d >= '0' && d <= '9'))
  in
  skip_ws ();
  let q = if !pos < len then read_int () else 0 in
  let q = max q 0 in
  let ids = Array.make q Uint63.zero in
  let ops = Array.make q Uint63.zero in
  let xs = Array.make q Uint63.zero in
  let ys = Array.make q Uint63.zero in
  let n = ref 0 in
  (try
     while !n < q do
       skip_ws ();
       if !pos >= len then raise Exit;
       let id = read_int () in
       skip_ws ();
       if !pos >= len then raise Exit;
       let op = Char.code (String.unsafe_get data !pos) in
       incr pos;
       let x = if int_ahead () then read_int () else 0 in
       let y = if int_ahead () then read_int () else 0 in
       let i = !n in
       ids.(i) <- Uint63.of_int id;
       ops.(i) <- Uint63.of_int op;
       xs.(i) <- Uint63.of_int x;
       ys.(i) <- Uint63.of_int y;
       incr n
     done
   with Exit -> ());
  let n = !n in
  let col a = Arr.of_array (Array.sub a 0 n) Uint63.zero in
  let out =
    run_commands (col ids) (col ops) (col xs) (col ys)
  in
  let buf = Buffer.create (1 lsl 16) in
  let m = Arr.length_to_int (Arr.length out) in
  for i = 0 to m - 1 do
    (match Arr.get out (Uint63.of_int i) with
     | None -> Buffer.add_char buf '-'
     | Some v -> Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 v))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
