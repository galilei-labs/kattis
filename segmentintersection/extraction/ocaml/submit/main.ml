(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Line Segment Intersection"                                  *)
(* (open.kattis.com/problems/segmentintersection).                     *)
(*                                                                     *)
(*   input   n (<= 10000), then n lines x1 y1 x2 y2 x3 y3 x4 y4,       *)
(*           |coordinate| <= 10000.                                    *)
(*   output  per case: "none", "X Y" or "X1 Y1 X2 Y2", 2 decimals.     *)
(*                                                                     *)
(* The extracted intersect returns the exact answer: a point is the    *)
(* rational (px/d, py/d) with d > 0, a segment has integer endpoints   *)
(* already ordered as the statement asks.  This wrapper rounds px/d to *)
(* hundredths, half away from zero, in integer arithmetic (|px|*200    *)
(* stays far below 2^62), and prints 0.00 rather than -0.00.  Words in *)
(* via Uint63.of_int, out via snd (Uint63.to_int2 _) (signed reading). *)
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
  let sg w = snd (Uint63.to_int2 w) in
  (* num/den (den > 0) rounded to hundredths, half away from zero *)
  let add_num num den =
    let a = abs num in
    let h = ((200 * a) + den) / (2 * den) in
    if h <> 0 && num < 0 then Buffer.add_char buf '-';
    Buffer.add_string buf (string_of_int (h / 100));
    Buffer.add_char buf '.';
    let f = h mod 100 in
    if f < 10 then Buffer.add_char buf '0';
    Buffer.add_string buf (string_of_int f)
  in
  let n = next_int () in
  for _ = 1 to n do
    let x1 = next_int () in let y1 = next_int () in
    let x2 = next_int () in let y2 = next_int () in
    let x3 = next_int () in let y3 = next_int () in
    let x4 = next_int () in let y4 = next_int () in
    let u = Uint63.of_int in
    (match
       intersect (u x1) (u y1) (u x2) (u y2)
         (u x3) (u y3) (u x4) (u y4)
     with
     | Empty -> Buffer.add_string buf "none"
     | Point (px, py, d) ->
       let d = sg d in
       add_num (sg px) d; Buffer.add_char buf ' '; add_num (sg py) d
     | Segment (ax, ay, bx, by_) ->
       add_num (sg ax) 1; Buffer.add_char buf ' ';
       add_num (sg ay) 1; Buffer.add_char buf ' ';
       add_num (sg bx) 1; Buffer.add_char buf ' ';
       add_num (sg by_) 1);
    Buffer.add_char buf '\n'
  done;
  print_string (Buffer.contents buf)
