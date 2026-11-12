
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Dimensional Analysis"                                       *)
(* (open.kattis.com/problems/dimensionalanalysis).                     *)
(*                                                                     *)
(*   input   N, then N equations "e1 = e2", atoms separated by " * "   *)
(*           or " / ", each atom 1 or a lowercase quantity name.       *)
(*   output  one line: valid or invalid.                               *)
(*                                                                     *)
(* Route arrays_bigint (Arr = Marray_raw): the extracted code works on  *)
(* plain OCaml arrays.  This part numbers the quantities in order of   *)
(* first appearance (m of them) and turns equation i into row i of     *)
(* length m: entry j = (times j is multiplied minus times divided) on  *)
(* the left side, minus the same count on the right side; the atom 1  *)
(* contributes nothing.  The rows are built once m is known.  Then one *)
(* call to the verified [valid].                                       *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let lines =
    List.filter (fun l -> l <> "")
      (List.map String.trim (String.split_on_char '\n' data))
  in
  let n, eqs =
    match lines with
    | first :: rest -> (int_of_string first, Array.of_list rest)
    | [] -> (0, [||])
  in
  let ids = Hashtbl.create 256 in
  let m = ref 0 in
  let id_of name =
    match Hashtbl.find_opt ids name with
    | Some j -> j
    | None ->
        let j = !m in
        Hashtbl.add ids name j;
        incr m;
        j
  in
  (* each equation as a list of (quantity, +1 / -1) contributions *)
  let contribs =
    Array.init n (fun i ->
        let toks = String.split_on_char ' ' eqs.(i) in
        let acc = ref [] in
        let side = ref 1 in
        let op = ref 1 in
        List.iter
          (fun t ->
            match t with
            | "" -> ()
            | "=" -> side := -1; op := 1
            | "*" -> op := 1
            | "/" -> op := -1
            | "1" -> ()
            | name -> acc := (id_of name, !side * !op) :: !acc)
          toks;
        !acc)
  in
  let m = !m in
  let rows =
    Array.map
      (fun cs ->
        let r = Array.make m 0 in
        List.iter (fun (j, c) -> r.(j) <- r.(j) + c) cs;
        Arr.of_array (Array.map Uint63.of_int r) Uint63.zero)
      contribs
  in
  let e = Arr.of_array rows (Arr.of_array [||] Uint63.zero) in
  let b = valid (Uint63.of_int m) e in
  print_string (if b then "valid\n" else "invalid\n")
