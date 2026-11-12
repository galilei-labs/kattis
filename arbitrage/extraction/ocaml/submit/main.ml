
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Arbitrage?" (open.kattis.com/problems/arbitrage).           *)
(*                                                                     *)
(*   input   several test cases, each: C (1 <= C <= 200), C distinct  *)
(*           3-letter codes, R, then R lines "SRC DST A:B"; a final    *)
(*           line with C = 0 ends the input.                           *)
(*   output  one line per case: "Arbitrage" or "Ok".                   *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml, tools/bigint.ml and the   *)
(* arrays_bigint extraction verbatim (Arr = Marray_raw).  This part is *)
(* the untrusted wrapper.  As in the spec, a currency is its 0-based   *)
(* position in the line of codes, and rate k is the k-th entry of the  *)
(* four parallel arrays src, dst, a, b (pay a_k of src_k, get b_k of   *)
(* dst_k).  No bignum crosses the interface (all inputs are <= 200 or  *)
(* <= 100), so Bigint is not called here.                              *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_sep c = c = ' ' || c = '\n' || c = '\r' || c = '\t' || c = ':' in
  (* next token: a maximal run of non-separator characters *)
  let next_tok () =
    while !pos < len && is_sep (String.unsafe_get data !pos) do incr pos done;
    let st = !pos in
    while !pos < len && not (is_sep (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data st (!pos - st)
  in
  let next_int () =
    let t = next_tok () in
    if t = "" then 0 else int_of_string t
  in
  let out = Buffer.create 1024 in
  let continue = ref true in
  while !continue do
    let c = next_int () in
    if c <= 0 then continue := false
    else begin
      let idx = Hashtbl.create (2 * c) in
      for i = 0 to c - 1 do
        Hashtbl.replace idx (next_tok ()) i
      done;
      let r = next_int () in
      let src = Array.make r Uint63.zero in
      let dst = Array.make r Uint63.zero in
      let a = Array.make r Uint63.zero in
      let b = Array.make r Uint63.zero in
      for k = 0 to r - 1 do
        let s = next_tok () in
        let d = next_tok () in
        src.(k) <- Uint63.of_int (Hashtbl.find idx s);
        dst.(k) <- Uint63.of_int (Hashtbl.find idx d);
        a.(k) <- Uint63.of_int (next_int ());
        b.(k) <- Uint63.of_int (next_int ())
      done;
      let res =
        arbitrage (Uint63.of_int c)
          (Arr.of_array src Uint63.zero) (Arr.of_array dst Uint63.zero)
          (Arr.of_array a Uint63.zero) (Arr.of_array b Uint63.zero)
      in
      Buffer.add_string out (if res then "Arbitrage\n" else "Ok\n")
    end
  done;
  print_string (Buffer.contents out)
