
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Non-negative Partial Sums" (problems/nonnegpartsums).       *)
(*                                                                     *)
(*   input   at most 110 cases: n (1 <= n <= 10^6), then n integers    *)
(*           in [-1000, 1000]; a line "0" ends the input.              *)
(*   output  one line per case: the number of good cyclic shifts.      *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml and the marray extraction verbatim.     *)
(* This part is the untrusted wrapper: read, convert, call once per    *)
(* case, print.  It does no arithmetic on the values.  stdin is read   *)
(* at once and scanned by hand; a negative value goes through          *)
(* Uint63.of_int and lands on the word whose signed reading it is.     *)
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
      c <> '-' && (c < '0' || c > '9')
    do
      incr pos
    done;
    let neg = !pos < len && String.unsafe_get data !pos = '-' in
    if neg then incr pos;
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
    if neg then - !v else !v
  in
  let out = Buffer.create 1024 in
  let rec loop () =
    if !pos < len then begin
      let n = next_int () in
      if n > 0 then begin
        let cells = Array.make n Uint63.zero in
        for i = 0 to n - 1 do
          cells.(i) <- Uint63.of_int (next_int ())
        done;
        let a = Arr.of_array cells Uint63.zero in
        let c = count_good_shifts a in
        Buffer.add_string out (string_of_int (snd (Uint63.to_int2 c)));
        Buffer.add_char out '\n';
        loop ()
      end
    end
  in
  loop ();
  print_string (Buffer.contents out)
