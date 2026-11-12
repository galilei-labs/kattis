
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Knapsack" (open.kattis.com/problems/knapsack).              *)
(*                                                                     *)
(*   input   1 to 30 test cases until end of file; each: C n, then n   *)
(*           lines "value weight".  C is read as a token through       *)
(*           float_of_string and truncated (the original statement     *)
(*           calls it a real; the bounds make it an integer).          *)
(*   output  per case: the number of items chosen, then a line with    *)
(*           their indices (0-based, any order).                       *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim +       *)
(* KnapsackImpl as `make extract` produced it).  This part is the      *)
(* untrusted wrapper: read, convert, call once per case, print.  The   *)
(* count printed is the length of the returned index array.            *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_tok c = (c >= '0' && c <= '9') || c = '.' || c = '-' || c = '+'
                 || c = 'e' || c = 'E' in
  let skip () =
    while !pos < len && not (is_tok (String.unsafe_get data !pos)) do
      incr pos
    done
  in
  let next_int () =
    skip ();
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
  let next_float_trunc () =
    skip ();
    let start = !pos in
    while !pos < len && is_tok (String.unsafe_get data !pos) do incr pos done;
    int_of_float (float_of_string (String.sub data start (!pos - start)))
  in
  let out = Buffer.create (1 lsl 16) in
  let rec cases () =
    skip ();
    if !pos < len then begin
      let c = next_float_trunc () in
      let n = next_int () in
      let vs = Array.make n Uint63.zero and ws = Array.make n Uint63.zero in
      for i = 0 to n - 1 do
        vs.(i) <- Uint63.of_int (next_int ());
        ws.(i) <- Uint63.of_int (next_int ())
      done;
      let (_best, idx) =
        knapsack (Uint63.of_int c)
          (Arr.of_array vs Uint63.zero) (Arr.of_array ws Uint63.zero)
      in
      let k = Arr.length_to_int (Arr.length idx) in
      Buffer.add_string out (string_of_int k);
      Buffer.add_char out '\n';
      for j = 0 to k - 1 do
        if j > 0 then Buffer.add_char out ' ';
        Buffer.add_string out
          (string_of_int (snd (Uint63.to_int2 (Arr.get idx (Uint63.of_int j)))))
      done;
      Buffer.add_char out '\n';
      cases ()
    end
  in
  cases ();
  print_string (Buffer.contents out)
