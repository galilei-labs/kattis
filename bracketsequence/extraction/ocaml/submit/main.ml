(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Bracket Sequence" (open.kattis.com/problems/bracketsequence)*)
(*                                                                     *)
(*   input   n (1 <= n <= 3*10^5), then n space-separated tokens, each *)
(*           "(", ")" or an integer 0 <= x < 10^9+7.                   *)
(*   output  one line: the value of the sequence modulo 10^9+7.        *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted code     *)
(* (route marray, [Arr] = Marray).  This part is the untrusted wrapper:*)
(* read, map each token to Open / Close / Num (Uint63.of_int x), call  *)
(* bracketsequence once, print.  No arithmetic on  *)
(* the values.                                                         *)
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
      c <> '(' && c <> ')' && (c < '0' || c > '9')
    do
      incr pos
    done
  in
  let read_int () =
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
  skip ();
  let n = read_int () in
  let cells = Array.make (max n 0) Open in
  for i = 0 to n - 1 do
    skip ();
    let c = if !pos < len then String.unsafe_get data !pos else ')' in
    if c = '(' then (cells.(i) <- Open; incr pos)
    else if c = ')' then (cells.(i) <- Close; incr pos)
    else cells.(i) <- Num (Uint63.of_int (read_int ()))
  done;
  let a = Arr.of_array cells Open in
  let r = bracketsequence a in
  print_string (string_of_int (Uint63.to_int_min r max_int));
  print_char '\n'
