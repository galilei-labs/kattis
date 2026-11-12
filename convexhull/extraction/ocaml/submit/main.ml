(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Convex Hull" (open.kattis.com/problems/convexhull).         *)
(*                                                                     *)
(*   input   several cases: n (1 <= n <= 10000), then n lines x y      *)
(*           (|x|, |y| <= 10000); a case with n = 0 ends the input.    *)
(*   output  per case: the hull's vertex count, then its vertices, one *)
(*           "x y" per line, counterclockwise, no collinear edges, any *)
(*           cyclic shift accepted.                                    *)
(*                                                                     *)
(* Everything above this comment comes from the pipeline (shim, then   *)
(* convex_hull as `make extract` produced it).  This    *)
(* part is the untrusted wrapper: read, convert, call once per case,   *)
(* print the points at the returned indices.  No geometry here.        *)
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
  let buf = Buffer.create (1 lsl 16) in
  let rec loop () =
    if !pos < len then begin
      let n = next_int () in
      if n > 0 then begin
        let xs = Array.make n 0 and ys = Array.make n 0 in
        for i = 0 to n - 1 do
          xs.(i) <- next_int ();
          ys.(i) <- next_int ()
        done;
        let ax = Arr.of_array (Array.map Uint63.of_int xs) Uint63.zero in
        let ay = Arr.of_array (Array.map Uint63.of_int ys) Uint63.zero in
        let h = convex_hull ax ay in
        let k = Arr.length_to_int (Arr.length h) in
        Buffer.add_string buf (string_of_int k);
        Buffer.add_char buf '\n';
        for j = 0 to k - 1 do
          let i = snd (Uint63.to_int2 (Arr.get h (Uint63.of_int j))) in
          Buffer.add_string buf (string_of_int xs.(i));
          Buffer.add_char buf ' ';
          Buffer.add_string buf (string_of_int ys.(i));
          Buffer.add_char buf '\n'
        done;
        loop ()
      end
    end
  in
  loop ();
  print_string (Buffer.contents buf)
