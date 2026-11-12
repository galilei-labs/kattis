
(* ------------------------------------------------------------------ *)
(* Part 3 of 3 of the Kattis submission file: the I/O driver.          *)
(*                                                                     *)
(* Kattis "Cuboid Slicing Game" (open.kattis.com/problems/             *)
(* cuboidslicinggame).                                                 *)
(*                                                                     *)
(*   input   RUBEN or ALBERT (who starts), then N (1 <= N <= 100),     *)
(*           then N lines x y z (1 <= x, y, z <= 30).                  *)
(*   output  one line: RUBEN or ALBERT, the winner under optimal play. *)
(*                                                                     *)
(* Above this comment: tools/kattis_shim.ml and the extracted code     *)
(* (winner) verbatim.  This part is the          *)
(* untrusted wrapper: read, convert, call once per game, print.  The   *)
(* statement describes one game per file; should a file hold several   *)
(* games back to back, each is answered on its own line.               *)
(* ------------------------------------------------------------------ *)

let () =
  let data = In_channel.input_all stdin in
  let len = String.length data in
  let pos = ref 0 in
  let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t' in
  let skip () =
    while !pos < len && is_space (String.unsafe_get data !pos) do incr pos done
  in
  let next_word () =
    skip ();
    let s = !pos in
    while !pos < len && not (is_space (String.unsafe_get data !pos)) do
      incr pos
    done;
    String.sub data s (!pos - s)
  in
  let next_int () = int_of_string (next_word ()) in
  let name = function Ruben -> "RUBEN" | Albert -> "ALBERT" in
  let buf = Buffer.create 64 in
  skip ();
  while !pos < len do
    let s =
      match next_word () with
      | "RUBEN" -> Ruben
      | "ALBERT" -> Albert
      | w -> failwith ("unexpected player name " ^ w)
    in
    let n = next_int () in
    let xs = Array.make n Uint63.zero in
    let ys = Array.make n Uint63.zero in
    let zs = Array.make n Uint63.zero in
    for i = 0 to n - 1 do
      xs.(i) <- Uint63.of_int (next_int ());
      ys.(i) <- Uint63.of_int (next_int ());
      zs.(i) <- Uint63.of_int (next_int ())
    done;
    let w =
      winner s
        (Arr.of_array xs Uint63.zero)
        (Arr.of_array ys Uint63.zero)
        (Arr.of_array zs Uint63.zero)
    in
    Buffer.add_string buf (name w);
    Buffer.add_char buf '\n';
    skip ()
  done;
  print_string (Buffer.contents buf)
