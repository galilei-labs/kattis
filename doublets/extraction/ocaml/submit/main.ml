
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Doublets" (open.kattis.com/problems/doublets).              *)
(*                                                                     *)
(*   input   the dictionary, one word per line, ended by an empty      *)
(*           line; then the query pairs, "src tgt" one per line.       *)
(*   output  per pair, a shortest chain one word per line, or the line *)
(*           "No solution."; a blank line between cases.               *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the marray extraction  *)
(* verbatim.  This part is the untrusted wrapper: read, convert, call  *)
(* doublets once on all queries, print.                   *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let lines = String.split_on_char '\n' data in
  let strip l =
    let n = String.length l in
    if n > 0 && l.[n - 1] = '\r' then String.sub l 0 (n - 1) else l
  in
  let lines = List.map strip lines in
  (* dictionary: up to the first empty line *)
  let rec dict acc = function
    | [] -> (List.rev acc, [])
    | "" :: rest -> (List.rev acc, rest)
    | w :: rest -> dict (String.trim w :: acc) rest
  in
  let words, rest = dict [] lines in
  let pairs =
    List.filter_map
      (fun l ->
        match List.filter (fun s -> s <> "")
                (String.split_on_char ' ' (String.trim l)) with
        | [ a; b ] -> Some (a, b)
        | _ -> None)
      rest
  in
  let ps s = Pstring.unsafe_of_string s in
  let d = Arr.of_array (Array.of_list (List.map ps words)) (ps "") in
  let src = Arr.of_array (Array.of_list (List.map (fun (a, _) -> ps a) pairs)) (ps "") in
  let tgt = Arr.of_array (Array.of_list (List.map (fun (_, b) -> ps b) pairs)) (ps "") in
  let res = doublets d src tgt in
  let b = Buffer.create 65536 in
  let q = List.length pairs in
  for k = 0 to q - 1 do
    if k > 0 then Buffer.add_char b '\n';
    (match Arr.get res (Uint63.of_int k) with
     | None -> Buffer.add_string b "No solution.\n"
     | Some c ->
       let n = snd (Uint63.to_int2 (Arr.length c)) in
       for i = 0 to n - 1 do
         Buffer.add_string b (Pstring.to_string (Arr.get c (Uint63.of_int i)));
         Buffer.add_char b '\n'
       done)
  done;
  print_string (Buffer.contents b)
