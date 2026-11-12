
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Palindromes" (open.kattis.com/problems/palindromes).        *)
(*                                                                     *)
(*   input   line 1: s, n lowercase letters (1 <= n <= 100 000);       *)
(*           line 2: m (1 <= m <= 100 000); then m lines "l r",        *)
(*           1 <= l <= r <= n.                                         *)
(*   output  m lines, the number of palindromic substrings of s[l..r]. *)
(*                                                                     *)
(* Everything above comes from the pipeline (tools/kattis_shim.ml and  *)
(* palindromes as `make extract` produced it, marray   *)
(* route).  This part is the untrusted wrapper: read all of stdin,     *)
(* scan by hand, convert, call once, print through a Buffer.  l and r  *)
(* are passed 1-based, as the spec keeps them.  Answers are at most    *)
(* n(n+1)/2 ~ 5e9, well inside a 63-bit word.                          *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* the name: the first maximal run of lowercase letters *)
  while !pos < len && (let c = String.unsafe_get data !pos in c < 'a' || c > 'z') do
    incr pos
  done;
  let start = !pos in
  while !pos < len && (let c = String.unsafe_get data !pos in c >= 'a' && c <= 'z') do
    incr pos
  done;
  let s = String.sub data start (!pos - start) in
  let next_int () =
    while !pos < len && (let c = String.unsafe_get data !pos in c < '0' || c > '9') do
      incr pos
    done;
    let v = ref 0 in
    while !pos < len && (let c = String.unsafe_get data !pos in c >= '0' && c <= '9') do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let m = next_int () in
  let ls = Array.make m Uint63.zero in
  let rs = Array.make m Uint63.zero in
  for k = 0 to m - 1 do
    ls.(k) <- Uint63.of_int (next_int ());
    rs.(k) <- Uint63.of_int (next_int ())
  done;
  let res =
    palindromes (Pstring.unsafe_of_string s)
      (Arr.of_array ls Uint63.zero) (Arr.of_array rs Uint63.zero)
  in
  let out = Buffer.create (m * 8) in
  for k = 0 to m - 1 do
    Buffer.add_string out
      (string_of_int (snd (Uint63.to_int2 (Arr.get res (Uint63.of_int k)))));
    Buffer.add_char out '\n'
  done;
  print_string (Buffer.contents out)
