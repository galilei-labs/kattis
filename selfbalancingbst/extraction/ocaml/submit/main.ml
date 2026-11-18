(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Self Balancing Binary Search Tree" (selfbalancingbst).      *)
(*                                                                     *)
(*   input   q, then q lines "<id> <op> [arg] [arg]".                  *)
(*   output  one line per r / g / z command: the number, or "-" when   *)
(*           the extracted function returns None (cursor unset).       *)
(*                                                                     *)
(* Characters select named operation constructors; each constructor   *)
(* carries exactly its required arguments. The wrapper reads, converts,*)
(* calls once, and prints. Negative values go through Uint63.of_int    *)
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
  let argument () =
    skip_blank ();
    Uint63.of_int (read_int ())
  in
  skip_ws ();
  let q = if !pos < len then read_int () else 0 in
  let q = max q 0 in
  let default = (Uint63.zero, GetSize) in
  let commands = Array.make q default in
  let n = ref 0 in
  (try
     while !n < q do
       skip_ws ();
       if !pos >= len then raise Exit;
       let id = read_int () in
       skip_ws ();
       if !pos >= len then raise Exit;
        let op = String.unsafe_get data !pos in
        incr pos;
        let operation = match op with
          | 'a' -> CopyFrom (argument ())
          | '?' -> FindKey (argument ())
          | 'l' -> LowerBound (argument ())
          | 'u' -> UpperBound (argument ())
          | 'i' -> let key = argument () in let value = argument () in Insert (key, value)
          | 'e' -> Erase
          | 'f' -> First
          | 'b' -> Last
          | '>' -> NextKey
          | '<' -> PreviousKey
          | 'k' -> SelectRank (argument ())
          | 'r' -> GetRank
          | 'g' -> GetValue
          | 's' -> SetValue (argument ())
          | 'z' -> GetSize
          | _ -> invalid_arg "unknown command"
        in
        commands.(!n) <- (Uint63.of_int id, operation);
       incr n
     done
   with Exit -> ());
  let n = !n in
  let out = run_commands (Arr.of_array (Array.sub commands 0 n) default) in
  let buf = Buffer.create (1 lsl 16) in
  let m = Arr.length_to_int (Arr.length out) in
  for i = 0 to m - 1 do
    (match Arr.get out (Uint63.of_int i) with
     | None -> Buffer.add_char buf '-'
     | Some v -> Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 v))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
