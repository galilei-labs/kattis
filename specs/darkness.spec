(* @function        darkness
   @signature       uint -> uint -> array (array uint) -> uint
   @math_signature  N -> N -> list (list N) -> N
   @summary         [darkness b h g] is the least amount, in pounds, of
                    fencing between side-adjacent cells of the club [g] (a
                    grid of bulb strengths under a ceiling of height [h])
                    that cuts every cell whose light level is below [b] off
                    from every border cell; a section costs 43 when both its
                    cells are lit, 11 otherwise. The light level of a cell is
                    the exact sum, over every bulb (its own included), of
                    s / (dr^2 + dc^2 + h^2).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray QArith Relations.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The club is the list of its R rows, each the list of the C
   bulb strengths of its cells; cell (i, j) is row i, column j. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

Definition rows (g : list (list N)) : N := len g.
Definition cols (g : list (list N)) : N := len (hd [] g).

Definition in_grid g (i j : N) : Prop := i < rows g /\ j < cols g.

Definition on_border g (i j : N) : Prop :=
  in_grid g i j /\ (i = 0 \/ i = rows g - 1 \/ j = 0 \/ j = cols g - 1).

(* The strength of the bulb above cell (i, j). *)
Definition strength g (i j : N) : N := nth (N.to_nat j) (nth (N.to_nat i) g []) 0.

(* f 0 + f 1 + ... + f (n - 1), in Q. *)
Fixpoint qsum (f : N -> Q) (n : nat) : Q :=
  match n with O => 0%Q | S m => (qsum f m + f (N.of_nat m))%Q end.

(* The light level, exactly, at the centre of cell (i, j): the bulb of every
   cell (i', j'), its own included, adds s / (dr^2 + dc^2 + h^2). *)
Definition light (h : N) g (i j : N) : Q :=
  qsum (fun i' => qsum (fun j' =>
    inject_Z (Z.of_N (strength g i' j')) /
    inject_Z ((Z.of_N i - Z.of_N i') ^ 2 + (Z.of_N j - Z.of_N j') ^ 2
              + Z.of_N h ^ 2))%Q
    (N.to_nat (cols g))) (N.to_nat (rows g)).

(* Cell (i, j) meets the minimum lighting standard b. *)
Definition lit (b h : N) g (i j : N) : bool :=
  Qle_bool (inject_Z (Z.of_N b)) (light h g i j).

(* A fencing: [hf i j] fences (i, j) off from (i, j+1), [vf i j] fences
   (i, j) off from (i+1, j); values off the internal sections are never
   read.  [step] is one move between side-adjacent cells through no fence. *)
Definition step (hf vf : N -> N -> bool) g (p q : N * N) : Prop :=
  let '(i, j) := p in let '(i', j') := q in
  in_grid g i j /\ in_grid g i' j' /\
  ((i' = i /\ j' = j + 1 /\ hf i j = false) \/
   (i' = i /\ j = j' + 1 /\ hf i j' = false) \/
   (i' = i + 1 /\ j' = j /\ vf i j = false) \/
   (i = i' + 1 /\ j' = j /\ vf i' j = false)).

(* No unfenced walk leads from a dark cell to a border cell. *)
Definition fences_out_dark (b h : N) g hf vf : Prop :=
  forall i j i' j', in_grid g i j -> lit b h g i j = false ->
  on_border g i' j' -> ~ clos_refl_trans _ (step hf vf g) (i, j) (i', j').

(* The price of the section between cells (i, j) and (i', j'). *)
Definition price (b h : N) g (i j i' j' : N) : N :=
  if lit b h g i j && lit b h g i' j' then 43 else 11.

(* f 0 + f 1 + ... + f (n - 1), in N. *)
Fixpoint nsum (f : N -> N) (n : nat) : N :=
  match n with O => 0 | S m => nsum f m + f (N.of_nat m) end.

(* The price of all the sections a fencing builds. *)
Definition cost (b h : N) g (hf vf : N -> N -> bool) : N :=
  nsum (fun i => nsum (fun j =>
     if hf i j then price b h g i j i (j + 1) else 0)
     (N.to_nat (cols g - 1))) (N.to_nat (rows g)) +
  nsum (fun i => nsum (fun j =>
     if vf i j then price b h g i j (i + 1) j else 0)
     (N.to_nat (cols g))) (N.to_nat (rows g - 1)).

(* The statement's bounds. *)
Record valid_input (b h : N) (g : list (list N)) : Prop := {
  (* an integer B (0 < B <= 9), the minimum required light level *)
  vi_b : 0 < b <= 9;
  (* an integer H (0 < H <= 5), the height of the ceiling *)
  vi_h : 0 < h <= 5;
  (* two integers R and C (0 < R, C <= 30) *)
  vi_r : 0 < rows g <= 30;
  vi_c : 0 < cols g <= 30;
  (* R further lines, each containing a string of C digits *)
  vi_rows : Forall (fun row => len row = cols g) g;
  vi_digits : Forall (Forall (fun s => s <= 9)) g;
  (* the 2(R+C)-4 cells along the borders of the club are sufficiently lit *)
  vi_border : forall i j, on_border g i j -> lit b h g i j = true;
}.

(* The answer is the least cost of a fencing that fences out the dark cells:
   some such fencing costs exactly o, and none costs less. *)
Definition darkness_spec (b h : N) g (o : N) : Prop :=
  (exists hf vf, fences_out_dark b h g hf vf /\ cost b h g hf vf = o) /\
  (forall hf vf, fences_out_dark b h g hf vf -> o <= cost b h g hf vf).

Program darkness : uint -> uint -> array (array uint) -> uint.

Specification darkness_correct :
  forall (b h : N) (g : list (list N)) (xb xh : uint) (xg : array (array uint)),
  valid_input b h g -> repr xb b -> repr xh h -> repr xg g ->
  exists o : N, repr (darkness xb xh xg) o /\ darkness_spec b h g o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
