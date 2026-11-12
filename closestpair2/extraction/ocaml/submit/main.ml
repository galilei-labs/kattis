
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Closest Pair" (open.kattis.com/problems/closestpair2).      *)
(*                                                                     *)
(*   input   several test cases: n (2 <= n <= 100 000), then n lines   *)
(*           "x y", coordinates with at most 2 decimals, |c| <= 1e5;   *)
(*           terminated by a case n = 0.                               *)
(*   output  per case one line x1 y1 x2 y2: any closest pair.          *)
(*                                                                     *)
(* Each coordinate text is parsed exactly into a whole number of       *)
(* hundredths ("1.12" -> 112, "-884.2" -> -88420, "158" -> 15800), the *)
(* spec's repr_hundredths, and lands on a sint word via Uint63.of_int. *)
(* The extracted closestpair returns two indices; the *)
(* driver prints the two points' coordinate texts exactly as they were *)
(* read (no float formatting).  No arithmetic on the values here.      *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let skip_blank () =
    while
      !pos < len
      &&
      let c = String.unsafe_get data !pos in
      c = ' ' || c = '\n' || c = '\r' || c = '\t'
    do
      incr pos
    done
  in
  let is_digit c = c >= '0' && c <= '9' in
  (* reads one number; returns its value in hundredths and its text span *)
  let next_num () =
    skip_blank ();
    let start = !pos in
    let neg =
      !pos < len
      && (let c = String.unsafe_get data !pos in
          if c = '-' || c = '+' then (incr pos; c = '-') else false)
    in
    let v = ref 0 in
    while !pos < len && is_digit (String.unsafe_get data !pos) do
      v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
      incr pos
    done;
    let frac = ref 0 in
    if !pos < len && String.unsafe_get data !pos = '.' then begin
      incr pos;
      while !pos < len && is_digit (String.unsafe_get data !pos) do
        if !frac < 2 then
          v := (!v * 10) + (Char.code (String.unsafe_get data !pos) - 48);
        incr frac;
        incr pos
      done
    end;
    for _ = min !frac 2 to 1 do v := !v * 10 done;
    ((if neg then - !v else !v), start, !pos - start)
  in
  let out = Buffer.create (1 lsl 16) in
  let rec loop () =
    skip_blank ();
    if !pos < len then begin
      let (n100, _, _) = next_num () in
      let n = n100 / 100 in
      if n > 0 then begin
        let xs = Array.make n Uint63.zero and ys = Array.make n Uint63.zero in
        let xt = Array.make n (0, 0) and yt = Array.make n (0, 0) in
        for i = 0 to n - 1 do
          let (x, xs0, xl) = next_num () in
          let (y, ys0, yl) = next_num () in
          xs.(i) <- Uint63.of_int x;
          ys.(i) <- Uint63.of_int y;
          xt.(i) <- (xs0, xl);
          yt.(i) <- (ys0, yl)
        done;
        let ax = Arr.of_array xs Uint63.zero and ay = Arr.of_array ys Uint63.zero in
        let (i, j) = closestpair ax ay in
        let i = snd (Uint63.to_int2 i) and j = snd (Uint63.to_int2 j) in
        let put (s, l) = Buffer.add_substring out data s l in
        put xt.(i); Buffer.add_char out ' ';
        put yt.(i); Buffer.add_char out ' ';
        put xt.(j); Buffer.add_char out ' ';
        put yt.(j); Buffer.add_char out '\n';
        loop ()
      end
    end
  in
  loop ();
  print_string (Buffer.contents out)
