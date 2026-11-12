(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Suffix Sorting" (suffixsorting).                            *)
(*                                                                     *)
(*   input   test cases until end of file; each is a line s (any       *)
(*           printable characters, spaces included, 1 <= |s| <= 1e5)   *)
(*           then a line "n q_1 .. q_n".                               *)
(*   output  per case one line: SA[q_1] .. SA[q_n], single spaces.     *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml and suffix_array as   *)
(* `make extract` produced it (marray route).  This part is the        *)
(* untrusted wrapper: read the whole of stdin, cut the string line by  *)
(* hand (a trailing '\r' is dropped), call once per case, index the    *)
(* result, print through a Buffer.                                     *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let read_line () =
    let start = !pos in
    while !pos < len && String.unsafe_get data !pos <> '\n' do incr pos done;
    let stop = !pos in
    if !pos < len then incr pos;
    let stop =
      if stop > start && String.unsafe_get data (stop - 1) = '\r' then stop - 1
      else stop in
    String.sub data start (stop - start)
  in
  let next_int () =
    while !pos < len &&
          (let c = String.unsafe_get data !pos in c < '0' || c > '9') do
      incr pos done;
    let v = ref 0 in
    while !pos < len &&
          (let c = String.unsafe_get data !pos in c >= '0' && c <= '9') do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    !v
  in
  let skip_to_eol () =
    while !pos < len && String.unsafe_get data !pos <> '\n' do incr pos done;
    if !pos < len then incr pos
  in
  let out = Buffer.create (1 lsl 16) in
  let continue = ref true in
  while !continue && !pos < len do
    let s = read_line () in
    if s = "" && !pos >= len then continue := false
    else begin
      let n = next_int () in
      let sa = suffix_array (Pstring.unsafe_of_string s) in
      for i = 0 to n - 1 do
        let q = next_int () in
        if i > 0 then Buffer.add_char out ' ';
        Buffer.add_string out
          (string_of_int (snd (Uint63.to_int2 (Arr.get sa (Uint63.of_int q)))))
      done;
      Buffer.add_char out '\n';
      skip_to_eol ()
    end
  done;
  print_string (Buffer.contents out)
