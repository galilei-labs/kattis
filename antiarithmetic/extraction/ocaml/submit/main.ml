(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Antiarithmetic?" (open.kattis.com/problems/antiarithmetic). *)
(*                                                                     *)
(*   input   at most 5 lines "n: p_0 p_1 ... p_{n-1}" (3 <= n <= 10^4, *)
(*           a permutation of 0..n-1), then a line "0".                *)
(*   output  one line per test case: yes (antiarithmetic) or no.       *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline: the shim     *)
(* (tools/kattis_shim.ml; [Arr] names the route's array module) and    *)
(* the extracted antiarithmetic verbatim.  This     *)
(* part is the untrusted wrapper: read, convert, call once per case,   *)
(* print.  stdin is read in one go and scanned by hand; the scanner    *)
(* skips every non-digit, so the colon after n needs no special case.  *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  (* -1 at end of input *)
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
  let out = Buffer.create 64 in
  let rec loop () =
    let n = next_int () in
    if n > 0 then begin
      let cells = Array.make n Uint63.zero in
      for i = 0 to n - 1 do
        cells.(i) <- Uint63.of_int (next_int ())
      done;
      let a = Arr.of_array cells Uint63.zero in
      Buffer.add_string out
        (if antiarithmetic a then "yes\n" else "no\n");
      loop ()
    end
  in
  loop ();
  print_string (Buffer.contents out)
