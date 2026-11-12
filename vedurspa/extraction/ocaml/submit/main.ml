(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Weather Forecast" (open.kattis.com/problems/vedurspa).      *)
(*                                                                     *)
(*   input   n m; one line of extra info (read and ignored); n lines   *)
(*           "t d s h", t and s reals with one decimal, d and h        *)
(*           integers, any of them "-" for a missing value.            *)
(*   output  m lines "t d s h" in the same format (scored problem).    *)
(*                                                                     *)
(* Everything above comes from the pipeline (shim, Bigint, the         *)
(* arrays_bigint extraction, Arr = Marray_raw).  This part reads,      *)
(* converts (float_of_string then Float64.of_float; Uint63.of_int),    *)
(* calls vedurspa once and prints: temperature and speed  *)
(* with "%.1f" ("-0.0" printed "0.0"), direction and humidity through  *)
(* snd (Uint63.to_int2 _), None as "-".  No arithmetic on the values.  *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let next_tok () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done;
    let st = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do incr pos done;
    String.sub data st (!pos - st)
  in
  let n = int_of_string (next_tok ()) in
  let m = int_of_string (next_tok ()) in
  (* skip the rest of the first line, then the whole extra-info line *)
  let skip_line () =
    while !pos < len && String.unsafe_get data !pos <> '\n' do incr pos done;
    if !pos < len then incr pos
  in
  skip_line ();
  skip_line ();
  let fl () =
    match next_tok () with
    | "-" -> None
    | s -> Some (Float64.of_float (float_of_string s))
  in
  let it () =
    match next_tok () with
    | "-" -> None
    | s -> Some (Uint63.of_int (int_of_string s))
  in
  let t = Array.make n None and d = Array.make n None
  and s = Array.make n None and h = Array.make n None in
  for i = 0 to n - 1 do
    t.(i) <- fl ();
    d.(i) <- it ();
    s.(i) <- fl ();
    h.(i) <- it ()
  done;
  let (((ot, od), os), oh) =
    vedurspa (Arr.of_array t None) (Arr.of_array d None)
      (Arr.of_array s None) (Arr.of_array h None) (Uint63.of_int m)
  in
  let b = Buffer.create (m * 20 + 16) in
  let pf = function
    | None -> Buffer.add_char b '-'
    | Some f ->
        let str = Printf.sprintf "%.1f" (Float64.to_float f) in
        Buffer.add_string b (if str = "-0.0" then "0.0" else str)
  in
  let pi = function
    | None -> Buffer.add_char b '-'
    | Some w -> Buffer.add_string b (string_of_int (snd (Uint63.to_int2 w)))
  in
  let k = Array.length ot in
  for j = 0 to k - 1 do
    pf ot.(j); Buffer.add_char b ' ';
    pi od.(j); Buffer.add_char b ' ';
    pf os.(j); Buffer.add_char b ' ';
    pi oh.(j); Buffer.add_char b '\n'
  done;
  print_string (Buffer.contents b)
