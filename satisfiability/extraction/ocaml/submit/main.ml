
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Yet Satisfiability Again!" (problems/satisfiability).       *)
(*                                                                     *)
(*   input   t (<= 5) test cases; each: "n m" (1 <= n <= 20,           *)
(*           1 <= m <= 100), then m clause lines, literals "Xi" or     *)
(*           "~Xi" (1 <= i <= n) separated by " v ".                   *)
(*   output  per case one line: satisfiable / unsatisfiable.           *)
(*                                                                     *)
(* Everything above comes from the pipeline (tools/kattis_shim.ml and  *)
(* the marray extraction verbatim).  This part is the untrusted        *)
(* wrapper: read, convert, call once per case, print.  Variable        *)
(* indices stay 1-based, as in the spec ([X i] is the statement's Xi). *)
(* The whole of stdin is read at once and split into lines; blank      *)
(* lines are skipped, and a clause is one line, scanned by hand.       *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let lines =
    List.filter (fun s -> String.trim s <> "") (String.split_on_char '\n' data)
    |> Array.of_list
  in
  let li = ref 0 in
  let next_line () = let s = lines.(!li) in incr li; s in
  (* the integers of a line, in order *)
  let ints s =
    let l = String.length s and acc = ref [] and i = ref 0 in
    while !i < l do
      if s.[!i] >= '0' && s.[!i] <= '9' then begin
        let v = ref 0 in
        while !i < l && s.[!i] >= '0' && s.[!i] <= '9' do
          v := (!v * 10) + (Char.code s.[!i] - 48); incr i
        done;
        acc := !v :: !acc
      end else incr i
    done;
    List.rev !acc
  in
  (* the literals of a clause line: "~X<d>" -> NotX d, "X<d>" -> X d *)
  let clause s =
    let l = String.length s and acc = ref [] and i = ref 0 in
    while !i < l do
      let c = s.[!i] in
      if c = '~' || c = 'X' then begin
        let neg = c = '~' in
        while !i < l && (s.[!i] < '0' || s.[!i] > '9') do incr i done;
        let v = ref 0 in
        while !i < l && s.[!i] >= '0' && s.[!i] <= '9' do
          v := (!v * 10) + (Char.code s.[!i] - 48); incr i
        done;
        let w = Uint63.of_int !v in
        acc := (if neg then NotX w else X w) :: !acc
      end else incr i
    done;
    Array.of_list (List.rev !acc)
  in
  let dflt = X Uint63.zero in
  let t = match ints (next_line ()) with t :: _ -> t | [] -> 0 in
  let buf = Buffer.create 256 in
  for _ = 1 to t do
    let n, m =
      match ints (next_line ()) with n :: m :: _ -> n, m | _ -> failwith "n m"
    in
    let cls = Array.init m (fun _ -> Arr.of_array (clause (next_line ())) dflt) in
    let y = Arr.of_array cls (Arr.of_array [||] dflt) in
    Buffer.add_string buf
      (if satisfiable (Uint63.of_int n) y
       then "satisfiable\n" else "unsatisfiable\n")
  done;
  print_string (Buffer.contents buf)
