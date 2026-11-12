
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "String Hashing" (open.kattis.com/problems/hashing).         *)
(*                                                                     *)
(*   input   S (letters a-z, 1 .. 300 000), then Q (0 .. 300 000),     *)
(*           then Q lines "L R" with 0 <= L < R <= |S|.                *)
(*   output  one line per query: a hash H(L, R), a non-negative 64-bit *)
(*           integer, equal for equal substrings.                      *)
(*                                                                     *)
(* Everything above this comment is the shim and HashingImpl exactly   *)
(* as `make extract` produced it.  This part is the untrusted wrapper: *)
(* read, draw the key, convert, call once, print.                      *)
(*                                                                     *)
(* The key r is drawn uniformly in [0, 2^61 - 1) (the spec's key       *)
(* range), from a self-initialised generator.  The hashes are < 2^61,  *)
(* so they are non-negative 64-bit integers and read back exactly with *)
(* [snd (Uint63.to_int2 _)].  Stdin is read in one go, scanned by hand; *)
(* the output goes through one Buffer.                                 *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* S: the first maximal run of letters. *)
  while !pos < len && (let c = String.unsafe_get data !pos in c < 'a' || c > 'z') do
    incr pos
  done;
  let s0 = !pos in
  while !pos < len && (let c = String.unsafe_get data !pos in c >= 'a' && c <= 'z') do
    incr pos
  done;
  let s = String.sub data s0 (!pos - s0) in
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
  let q = next_int () in
  let ls = Array.make q Uint63.zero in
  let rs = Array.make q Uint63.zero in
  for i = 0 to q - 1 do
    ls.(i) <- Uint63.of_int (next_int ());
    rs.(i) <- Uint63.of_int (next_int ())
  done;
  Random.self_init ();
  let key = Random.full_int ((1 lsl 61) - 1) in
  let h =
    hashes (Uint63.of_int key) (Pstring.unsafe_of_string s)
      (Arr.of_array ls Uint63.zero) (Arr.of_array rs Uint63.zero)
  in
  let buf = Buffer.create (q * 20 + 16) in
  for i = 0 to q - 1 do
    Buffer.add_string buf
      (string_of_int (snd (Uint63.to_int2 (Arr.get h (Uint63.of_int i)))));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
