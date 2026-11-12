(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Road Times" (open.kattis.com/problems/roadtimes).           *)
(*                                                                     *)
(*   input   n, the n x n distance matrix (-1: no road), r, r lines    *)
(*           s d t, q, q lines s d.                                    *)
(*   output  one line per query: s d low high (bounds in minutes,      *)
(*           judged within absolute or relative error 1e-6).           *)
(*                                                                     *)
(* Route arrays_bigint: Arr = Marray_raw (plain OCaml arrays), Z onto  *)
(* Bigint.  This part is the untrusted wrapper: read, convert, call    *)
(* once, print.  -1 goes through Uint63.of_int and lands on the word   *)
(* whose signed reading is -1 (sint).  The query's s and d are echoed  *)
(* from the input; the bounds are printed with %.9f.                   *)
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
  let n = next_int () in
  let rows =
    Array.init n (fun _ ->
        let row = Array.init n (fun _ -> Uint63.of_int (next_int ())) in
        Arr.of_array row Uint63.zero)
  in
  let empty_row = Arr.of_array [||] Uint63.zero in
  let dist = Arr.of_array rows empty_row in
  let r = next_int () in
  let rs = Array.make r Uint63.zero in
  let rd = Array.make r Uint63.zero in
  let rt = Array.make r Uint63.zero in
  for k = 0 to r - 1 do
    let s = next_int () in
    let d = next_int () in
    let t = next_int () in
    rs.(k) <- Uint63.of_int s;
    rd.(k) <- Uint63.of_int d;
    rt.(k) <- Uint63.of_int t
  done;
  let q = next_int () in
  let qs = Array.make q 0 in
  let qd = Array.make q 0 in
  for j = 0 to q - 1 do
    let s = next_int () in
    let d = next_int () in
    qs.(j) <- s;
    qd.(j) <- d
  done;
  let conv a = Arr.of_array (Array.map Uint63.of_int a) Uint63.zero in
  let res =
    roadtimes dist
      (Arr.of_array rs Uint63.zero) (Arr.of_array rd Uint63.zero)
      (Arr.of_array rt Uint63.zero) (conv qs) (conv qd)
  in
  let buf = Buffer.create (64 * (q + 1)) in
  for j = 0 to q - 1 do
    let (lo, hi) = Arr.get res (Uint63.of_int j) in
    Buffer.add_string buf
      (Printf.sprintf "%d %d %.9f %.9f\n" qs.(j) qd.(j)
         (Float64.to_float lo) (Float64.to_float hi))
  done;
  print_string (Buffer.contents buf)
