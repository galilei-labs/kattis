
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Knapsack in a Globalized World" (problems/knapsack2).       *)
(*                                                                     *)
(*   input   n k (1 <= n <= 20, 1 <= k <= 10^18), then n sizes g_i     *)
(*           (1 <= g_i <= 1000).                                       *)
(*   output  one word: "possible" or "impossible".                     *)
(*                                                                     *)
(* Above: tools/kattis_shim.ml and Knapsack2Impl as `make extract`     *)
(* produced it (marray route). This part is the untrusted wrapper:     *)
(* read, convert, call once, print. k <= 10^18 fits in OCaml's int.    *)
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
  let n = next_int () in
  let k = next_int () in
  let cells = Array.make (max n 0) Uint63.zero in
  for i = 0 to n - 1 do
    cells.(i) <- Uint63.of_int (next_int ())
  done;
  let g = Arr.of_array cells Uint63.zero in
  print_string
    (if fillable (Uint63.of_int k) g then "possible"
     else "impossible");
  print_char '\n'
