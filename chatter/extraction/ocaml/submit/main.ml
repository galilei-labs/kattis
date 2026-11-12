
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Chatter" (open.kattis.com/problems/chatter).                *)
(*                                                                     *)
(*   input   up to 1 000 lines, each five integers n r a b c, until    *)
(*           end of file.                                              *)
(*   output  per line: the number of groups, then each distinct group *)
(*           size from largest to smallest, as "s" when one group has  *)
(*           that size, "sxk" when k > 1 groups do.                    *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted          *)
(* ChatterImpl (marray route).  This part reads, converts, calls       *)
(* chatter once per line and prints; no arithmetic.        *)
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
      c < '0' || c > '9'
    do
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
  let buf = Buffer.create (1 lsl 16) in
  let word w = snd (Uint63.to_int2 w) in
  skip ();
  while !pos < len do
    let n = next_int () in
    let r = next_int () in
    let a = next_int () in
    let b = next_int () in
    let c = next_int () in
    let (g, t) =
      chatter (Uint63.of_int n) (Uint63.of_int r)
        (Uint63.of_int a) (Uint63.of_int b) (Uint63.of_int c)
    in
    Buffer.add_string buf (string_of_int (word g));
    let m = word (Arr.length t) in
    for i = 0 to m - 1 do
      let (s, k) = Arr.get t (Uint63.of_int i) in
      Buffer.add_char buf ' ';
      Buffer.add_string buf (string_of_int (word s));
      let k = word k in
      if k > 1 then begin
        Buffer.add_char buf 'x';
        Buffer.add_string buf (string_of_int k)
      end
    done;
    Buffer.add_char buf '\n';
    skip ()
  done;
  print_string (Buffer.contents buf)
