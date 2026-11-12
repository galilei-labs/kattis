
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Longest Increasing Subsequence" (longincsubseq).            *)
(*                                                                     *)
(*   input   1 to 64 test cases until end of file; each: n             *)
(*           (1 <= n <= 100 000), then n integers in [-2^31, 2^31).    *)
(*   output  per case: the length of a longest strictly increasing     *)
(*           subsequence, then its 0-based indices in ascending order. *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* LongincsubseqImpl as `make extract` produced it).  This part is the *)
(* untrusted wrapper: read, convert, call once per case, print.        *)
(* Values go in through Uint63.of_int (a negative lands on the word    *)
(* whose signed reading is that number); indices come back through     *)
(* [snd (Uint63.to_int2 _)].  Output is accumulated in one Buffer.     *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let skip () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c <> '-' && (c < '0' || c > '9')
    do
      incr pos
    done
  in
  let next_int () =
    skip ();
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
  let out = Buffer.create (1 lsl 20) in
  skip ();
  while !pos < len do
    let n = next_int () in
    let cells = Array.make (max n 0) Uint63.zero in
    for i = 0 to n - 1 do
      cells.(i) <- Uint63.of_int (next_int ())
    done;
    let a = Arr.of_array cells Uint63.zero in
    let s = lis a in
    let k = Arr.length_to_int (Arr.length s) in
    Buffer.add_string out (string_of_int k);
    Buffer.add_char out '\n';
    for t = 0 to k - 1 do
      if t > 0 then Buffer.add_char out ' ';
      Buffer.add_string out
        (string_of_int (snd (Uint63.to_int2 (Arr.get s (Uint63.of_int t)))))
    done;
    Buffer.add_char out '\n';
    skip ()
  done;
  print_string (Buffer.contents out)
