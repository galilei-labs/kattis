
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Minimum Spanning Tree" (open.kattis.com/problems/minspantree)*)
(*                                                                     *)
(*   input   test cases "n m" then m lines "u v w", until "0 0".       *)
(*   output  per case: "Impossible", or the weight then the tree's     *)
(*           edges "x y" (x < y), sorted lexicographically.            *)
(*                                                                     *)
(* Untrusted wrapper: read, convert, call mst once per *)
(* case, print.  It orders each edge's endpoints and sorts the pairs   *)
(* (output format only); the tree and its weight come from the         *)
(* extracted code (edge indices are 0-based).                          *)
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
  let buf = Buffer.create (1 lsl 20) in
  let rec loop () =
    if !pos >= len then ()
    else begin
      let n = next_int () in
      let m = next_int () in
      if n = 0 && m = 0 then ()
      else begin
        let us = Array.make m 0 and vs = Array.make m 0 in
        let ws = Array.make m Uint63.zero in
        for k = 0 to m - 1 do
          us.(k) <- next_int ();
          vs.(k) <- next_int ();
          ws.(k) <- Uint63.of_int (next_int ())
        done;
        let au = Arr.of_array (Array.map Uint63.of_int us) Uint63.zero in
        let av = Arr.of_array (Array.map Uint63.of_int vs) Uint63.zero in
        let aw = Arr.of_array ws Uint63.zero in
        (match mst (Uint63.of_int n) au av aw with
         | None -> Buffer.add_string buf "Impossible\n"
         | Some (c, t) ->
           Buffer.add_string buf (string_of_int (snd (Uint63.to_int2 c)));
           Buffer.add_char buf '\n';
           let l = Arr.length_to_int (Arr.length t) in
           let pairs =
             Array.init l (fun i ->
                 let k = snd (Uint63.to_int2 (Arr.get t (Uint63.of_int i))) in
                 let a = us.(k) and b = vs.(k) in
                 if a < b then (a, b) else (b, a))
           in
           Array.sort compare pairs;
           Array.iter
             (fun (a, b) ->
               Buffer.add_string buf (string_of_int a);
               Buffer.add_char buf ' ';
               Buffer.add_string buf (string_of_int b);
               Buffer.add_char buf '\n')
             pairs);
        loop ()
      end
    end
  in
  loop ();
  print_string (Buffer.contents buf)
