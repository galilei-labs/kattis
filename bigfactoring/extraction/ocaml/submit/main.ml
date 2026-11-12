(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Big Factoring" (open.kattis.com/problems/bigfactoring).     *)
(*                                                                     *)
(*   input   one line: n, 2 <= n <= 10^24.                             *)
(*   output  one line: the prime factors of n in ascending order, with *)
(*           multiplicity, separated by single spaces.                 *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml, tools/bigint.ml and the   *)
(* arrays_bigint extraction (Z onto Bigint, arrays as OCaml arrays;    *)
(* [Arr] = Marray_raw).  This part is the untrusted wrapper: read the  *)
(* digits, Bigint.of_string, call once, print with Bigint.to_string.   *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let i = ref 0 in
  while !i < len && (data.[!i] < '0' || data.[!i] > '9') do incr i done;
  let j = ref !i in
  while !j < len && data.[!j] >= '0' && data.[!j] <= '9' do incr j done;
  let n = Bigint.of_string (String.sub data !i (!j - !i)) in
  let fs = bigfactoring n in
  let b = Buffer.create 256 in
  Array.iteri
    (fun k f ->
      if k > 0 then Buffer.add_char b ' ';
      Buffer.add_string b (Bigint.to_string f))
    fs;
  Buffer.add_char b '\n';
  print_string (Buffer.contents b)
