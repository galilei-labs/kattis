(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Relatives" (open.kattis.com/problems/relatives).            *)
(*                                                                     *)
(*   input   up to 10 lines, each one n (1 <= n <= 10^9), then a line *)
(*           "0".                                                      *)
(*   output  per case one line: the count of 1 <= k < n coprime to n.  *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml and the marray extraction verbatim.     *)
(* This part is the untrusted wrapper: read, convert, call once per    *)
(* case, print.  It does no arithmetic on the values.                  *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* Returns -1 at end of input. *)
  let next_int () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c < '0' || c > '9'
    do
      incr pos
    done;
    if !pos >= len then -1
    else begin
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
    end
  in
  let buf = Buffer.create 256 in
  let rec loop () =
    let n = next_int () in
    if n > 0 then begin
      let r = relatives (Uint63.of_int n) in
      Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 r)));
      Buffer.add_char buf '\n';
      loop ()
    end
  in
  loop ();
  print_string (Buffer.contents buf)
