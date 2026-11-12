(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Kingpin Escape" (open.kattis.com/problems/kingpinescape).   *)
(*                                                                     *)
(*   input   n h, then n-1 lines a b (the tree's passageways).         *)
(*   output  m, then m lines a b: the passageways to add (any minimum  *)
(*           set is accepted).                                         *)
(*                                                                     *)
(* Untrusted wrapper: read all of stdin, scan by hand, convert the two *)
(* columns with Arr.of_array, call kingpin_escape    *)
(* once, print the two result columns through a Buffer.                *)
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
  let h = next_int () in
  let m = max (n - 1) 0 in
  let ea = Array.make m Uint63.zero in
  let eb = Array.make m Uint63.zero in
  for i = 0 to m - 1 do
    ea.(i) <- Uint63.of_int (next_int ());
    eb.(i) <- Uint63.of_int (next_int ())
  done;
  let (xs, ys) =
    kingpin_escape (Uint63.of_int n) (Uint63.of_int h)
      (Arr.of_array ea Uint63.zero) (Arr.of_array eb Uint63.zero)
  in
  let k = Arr.length_to_int (Arr.length xs) in
  let out = Buffer.create (16 * (k + 1)) in
  let word w = Buffer.add_string out (string_of_int (snd (Uint63.to_int2 w))) in
  Buffer.add_string out (string_of_int k);
  Buffer.add_char out '\n';
  for i = 0 to k - 1 do
    word (Arr.get xs (Uint63.of_int i));
    Buffer.add_char out ' ';
    word (Arr.get ys (Uint63.of_int i));
    Buffer.add_char out '\n'
  done;
  print_string (Buffer.contents out)
