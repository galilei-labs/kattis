
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Odd Man Out" (open.kattis.com/problems/oddmanout).          *)
(*                                                                     *)
(*   input   N (1 <= N <= 50), then N cases: G (3 <= G < 1000), then   *)
(*           G codes C, 0 < C < 2^31.                                  *)
(*   output  one line per case: "Case #k: C" for the lone guest.       *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the array module of the route)   *)
(* and odd_one exactly as `make extract` produced it.    *)
(* This part is the untrusted wrapper: read, convert, call once per    *)
(* case, print.  It does no arithmetic on the codes.                   *)
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
  let buf = Buffer.create 4096 in
  let n = next_int () in
  for k = 1 to n do
    let g = next_int () in
    let cells = Array.make (max g 0) Uint63.zero in
    for i = 0 to g - 1 do
      cells.(i) <- Uint63.of_int (next_int ())
    done;
    let a = Arr.of_array cells Uint63.zero in
    let x = odd_one a in
    Buffer.add_string buf "Case #";
    Buffer.add_string buf (string_of_int k);
    Buffer.add_string buf ": ";
    Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 x)));
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
