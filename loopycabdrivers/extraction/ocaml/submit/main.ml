
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Loopy Cab Drivers" (open.kattis.com/problems/loopycabdrivers).*)
(*                                                                     *)
(*   input   n (0 <= n <= 10 000), then n lines "A B" of store names   *)
(*           (1..20 letters): a one-way street from A to B.            *)
(*   output  one line "okay s1 s2 ..." per group (groups and stores in *)
(*           lexicographic order), then "avoid s1 s2 ..." if any store *)
(*           is in no group.                                           *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the marray extraction  *)
(* verbatim.  This part is the untrusted wrapper: read the two columns *)
(* into two string arrays, call loopy_regions once, print.  All orders *)
(* come from the verified code (character codes, as strcmp).           *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_word () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let st = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data st (!pos - st)
  in
  let n = int_of_string (next_word ()) in
  let src = Array.make n "" and dst = Array.make n "" in
  for i = 0 to n - 1 do
    src.(i) <- next_word ();
    dst.(i) <- next_word ()
  done;
  let conv a =
    Arr.of_array (Array.map Pstring.unsafe_of_string a)
      (Pstring.unsafe_of_string "")
  in
  let (groups, avoid) = loopy_regions (conv src) (conv dst) in
  let b = Buffer.create 65536 in
  let words w a =
    Buffer.add_string b w;
    for j = 0 to Arr.length_to_int (Arr.length a) - 1 do
      Buffer.add_char b ' ';
      Buffer.add_string b (Pstring.to_string (Arr.get a (Uint63.of_int j)))
    done;
    Buffer.add_char b '\n'
  in
  for i = 0 to Arr.length_to_int (Arr.length groups) - 1 do
    words "okay" (Arr.get groups (Uint63.of_int i))
  done;
  if Arr.length_to_int (Arr.length avoid) > 0 then words "avoid" avoid;
  print_string (Buffer.contents b)
