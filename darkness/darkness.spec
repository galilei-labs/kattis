(* @function        darkness
   @signature       uint -> uint -> array (array uint) -> uint
   @math_signature  N -> N -> list (list N) -> N
   @summary         [darkness min_light ceiling_height club] is the least
                    amount, in pounds, of fencing between side-adjacent cells
                    of the club [club] (a grid of bulb strengths under a
                    ceiling of height [ceiling_height]) that cuts every cell
                    whose light level is below [min_light] off from every
                    border cell; a section costs 43 when both its cells are
                    lit, 11 otherwise. The light level of a cell is the exact
                    sum, over every bulb (its own included), of
                    s / (dr^2 + dc^2 + ceiling_height^2).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray QArith Relations.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The club is the list of its R rows, each the list of the C
   bulb strengths of its cells; cell (i, j) is row i, column j. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

Definition rows (club : list (list N)) : N := len club.
Definition cols (club : list (list N)) : N := len (hd [] club).

Definition in_grid club (i j : N) : Prop := i < rows club /\ j < cols club.

Definition on_border club (i j : N) : Prop :=
  in_grid club i j /\
  (i = 0 \/ i = rows club - 1 \/ j = 0 \/ j = cols club - 1).

(* The strength of the bulb above cell (i, j). *)
Definition strength club (i j : N) : N :=
  nth (N.to_nat j) (nth (N.to_nat i) club []) 0.

(* term 0 + term 1 + ... + term (term_count - 1), in Q. *)
Fixpoint qsum (term : N -> Q) (term_count : nat) : Q :=
  match term_count with
  | O => 0%Q
  | S previous => (qsum term previous + term (N.of_nat previous))%Q
  end.

(* The light level, exactly, at the centre of cell (i, j): the bulb of every
   cell (i', j'), its own included, adds
   s / (dr^2 + dc^2 + ceiling_height^2). *)
Definition light (ceiling_height : N) club (i j : N) : Q :=
  qsum (fun i' => qsum (fun j' =>
    inject_Z (Z.of_N (strength club i' j')) /
    inject_Z ((Z.of_N i - Z.of_N i') ^ 2 + (Z.of_N j - Z.of_N j') ^ 2
              + Z.of_N ceiling_height ^ 2))%Q
    (N.to_nat (cols club))) (N.to_nat (rows club)).

(* Cell (i, j) meets the minimum lighting standard min_light. *)
Definition lit (min_light ceiling_height : N) club (i j : N) : bool :=
  Qle_bool (inject_Z (Z.of_N min_light)) (light ceiling_height club i j).

(* A fencing: [h_fences i j] fences (i, j) off from (i, j+1), [v_fences i j]
   fences (i, j) off from (i+1, j); values off the internal sections are
   never read.  [step] is one move between side-adjacent cells through no
   fence. *)
Definition step (h_fences v_fences : N -> N -> bool) club (cell cell' : N * N)
    : Prop :=
  let '(i, j) := cell in let '(i', j') := cell' in
  in_grid club i j /\ in_grid club i' j' /\
  ((i' = i /\ j' = j + 1 /\ h_fences i j = false) \/
   (i' = i /\ j = j' + 1 /\ h_fences i j' = false) \/
   (i' = i + 1 /\ j' = j /\ v_fences i j = false) \/
   (i = i' + 1 /\ j' = j /\ v_fences i' j = false)).

(* No unfenced walk leads from a dark cell to a border cell. *)
Definition fences_out_dark (min_light ceiling_height : N) club
    h_fences v_fences : Prop :=
  forall i j i' j', in_grid club i j ->
  lit min_light ceiling_height club i j = false ->
  on_border club i' j' ->
  ~ clos_refl_trans _ (step h_fences v_fences club) (i, j) (i', j').

(* The price of the section between cells (i, j) and (i', j'). *)
Definition price (min_light ceiling_height : N) club (i j i' j' : N) : N :=
  if lit min_light ceiling_height club i j &&
     lit min_light ceiling_height club i' j' then 43 else 11.

(* term 0 + term 1 + ... + term (term_count - 1), in N. *)
Fixpoint nsum (term : N -> N) (term_count : nat) : N :=
  match term_count with
  | O => 0
  | S previous => nsum term previous + term (N.of_nat previous)
  end.

(* The price of all the sections a fencing builds. *)
Definition cost (min_light ceiling_height : N) club
    (h_fences v_fences : N -> N -> bool) : N :=
  nsum (fun i => nsum (fun j =>
     if h_fences i j then price min_light ceiling_height club i j i (j + 1)
     else 0)
     (N.to_nat (cols club - 1))) (N.to_nat (rows club)) +
  nsum (fun i => nsum (fun j =>
     if v_fences i j then price min_light ceiling_height club i j (i + 1) j
     else 0)
     (N.to_nat (cols club))) (N.to_nat (rows club - 1)).

(* The statement's bounds. *)
Record valid_input (min_light ceiling_height : N) (club : list (list N))
    : Prop := {
  (* an integer B (0 < B <= 9), the minimum required light level *)
  vi_b : 0 < min_light <= 9;
  (* an integer H (0 < H <= 5), the height of the ceiling *)
  vi_h : 0 < ceiling_height <= 5;
  (* two integers R and C (0 < R, C <= 30) *)
  vi_r : 0 < rows club <= 30;
  vi_c : 0 < cols club <= 30;
  (* R further lines, each containing a string of C digits *)
  vi_rows : Forall (fun row => len row = cols club) club;
  vi_digits : Forall (Forall (fun bulb => bulb <= 9)) club;
  (* the 2(R+C)-4 cells along the borders of the club are sufficiently lit *)
  vi_border : forall i j, on_border club i j ->
    lit min_light ceiling_height club i j = true;
}.

(* The answer is the least cost of a fencing that fences out the dark cells:
   some such fencing costs exactly output, and none costs less. *)
Definition darkness_spec (min_light ceiling_height : N) club
    (output : N) : Prop :=
  (exists h_fences v_fences,
     fences_out_dark min_light ceiling_height club h_fences v_fences /\
     cost min_light ceiling_height club h_fences v_fences = output) /\
  (forall h_fences v_fences,
     fences_out_dark min_light ceiling_height club h_fences v_fences ->
     output <= cost min_light ceiling_height club h_fences v_fences).

Program darkness : uint -> uint -> array (array uint) -> uint.

Specification darkness_correct :
  forall (min_light ceiling_height : N) (club : list (list N))
         (min_light_int ceiling_height_int : uint)
         (club_arr : array (array uint)),
  valid_input min_light ceiling_height club ->
  repr min_light_int min_light -> repr ceiling_height_int ceiling_height ->
  repr club_arr club ->
  exists output : N,
    repr (darkness min_light_int ceiling_height_int club_arr) output /\
    darkness_spec min_light ceiling_height club output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
