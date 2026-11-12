
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Booking" (open.kattis.com/problems/booking).                *)
(*                                                                     *)
(*   input   T; per case "B C", then B lines                           *)
(*           "code YYYY-MM-DD HH:MM YYYY-MM-DD HH:MM".                 *)
(*   output  per case, the minimum number of rooms on one line.        *)
(*                                                                     *)
(* Untrusted wrapper: read, convert, call min_rooms once   *)
(* per case, print.  The reservation code (alphanumeric, may start     *)
(* with a digit) is skipped as a whole token; each date is split by    *)
(* hand into the spec's datetime fields.  No arithmetic on the values. *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_digit c = c >= '0' && c <= '9' in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let skip_spaces () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done
  in
  (* Skips leading blanks, then reads digits; stops at any non-digit
     (so '-' and ':' end a field). *)
  let next_int () =
    skip_spaces ();
    let v = ref 0 in
    while !pos < len && is_digit (String.unsafe_get data !pos) do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let skip_token () =
    skip_spaces ();
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do
      incr pos
    done
  in
  let sep () = incr pos in (* the '-' or ':' between two fields *)
  let next_datetime () =
    let y = next_int () in sep ();
    let mo = next_int () in sep ();
    let d = next_int () in
    let h = next_int () in sep ();
    let mi = next_int () in
    { year = Uint63.of_int y; month = Uint63.of_int mo; day = Uint63.of_int d;
      hour = Uint63.of_int h; minute = Uint63.of_int mi }
  in
  let zero_dt =
    { year = Uint63.zero; month = Uint63.zero; day = Uint63.zero;
      hour = Uint63.zero; minute = Uint63.zero } in
  let out = Buffer.create 1024 in
  let t = next_int () in
  for _ = 1 to t do
    let b = next_int () in
    let c = next_int () in
    let arr = Array.make b zero_dt in
    let dep = Array.make b zero_dt in
    for i = 0 to b - 1 do
      skip_token ();
      arr.(i) <- next_datetime ();
      dep.(i) <- next_datetime ()
    done;
    let xa = Arr.of_array arr zero_dt in
    let xd = Arr.of_array dep zero_dt in
    let k = min_rooms (Uint63.of_int c) xa xd in
    Buffer.add_string out (string_of_int (snd (Uint63.to_int2 k)));
    Buffer.add_char out '\n'
  done;
  print_string (Buffer.contents out)
