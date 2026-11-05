(* @function        winner
   @signature       player -> array uint -> array uint -> array uint -> player
   @math_signature  player -> list N -> list N -> list N -> player
   @summary         [winner s xs ys zs] is the player who wins the Cuboid
                    Slicing Game when [s] moves first from the cuboids
                    xs_i x ys_i x zs_i and both play optimally. A move cuts
                    one cuboid along three planes through it, leaving up to 8
                    smaller cuboids; the player who removes the last cuboid
                    wins.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* The two names of the input and of the output line; a type of the
   problem's own, the same on both sides. *)
Inductive player := Ruben | Albert.

Instance repr_player : Repr player player := fun x i => x = i.

Definition opponent (p : player) : player :=
  match p with Ruben => Albert | Albert => Ruben end.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* A cuboid x * y * z, and a position of the game: the cuboids on the table. *)
Definition cuboid : Type := (N * N * N)%type.
Definition position : Type := list cuboid.

(* Cutting a side of length x at plane a (1 <= a <= x) leaves a-1 and x-a. *)
Definition sides (x a : N) : list N := [a - 1; x - a].

(* The up to 8 cuboids left when x * y * z is cut at planes a, b and c:
   every combination of the remaining sides, those with a side 0 dropped. *)
Definition pieces (x y z a b c : N) : position :=
  filter (fun '(p, q, r) => ((0 <? p) && (0 <? q) && (0 <? r))%bool)
    (flat_map (fun p => flat_map (fun q => map (fun r => (p, q, r))
       (sides z c)) (sides y b)) (sides x a)).

(* A legal move: choose a cuboid and three planes on it, and replace the
   cuboid by its pieces. *)
Inductive move : position -> position -> Prop :=
  | move_cut : forall l r x y z a b c,
      1 <= a <= x -> 1 <= b <= y -> 1 <= c <= z ->
      move (l ++ (x, y, z) :: r) (l ++ pieces x y z a b c ++ r).

(* Optimal play: the player to move wins iff some move leads to a position
   lost for the player to move then; it loses iff every move leads to a won
   position (so the empty position, where the opponent removed the last
   cuboid, is lost). *)
Inductive wins : position -> Prop :=
  | wins_move : forall p q, move p q -> loses q -> wins p
with loses : position -> Prop :=
  | loses_all : forall p, (forall q, move p q -> wins q) -> loses p.

(* The starting position: cuboid i is xs_i * ys_i * zs_i, in input order. *)
Definition initial (xs ys zs : list N) : position :=
  combine (combine xs ys) zs.

(* The statement's bounds; the N input lines are the three parallel lists
   of the coordinates x, y, z. *)
Record valid_input (xs ys zs : list N) : Prop := {
  (* 1 <= N <= 100 *)
  vi_n : 1 <= len xs <= 100;
  (* each of the N lines holds the three numbers x, y and z *)
  vi_ys_len : len ys = len xs;
  vi_zs_len : len zs = len xs;
  (* 1 <= x, y, z <= 30 *)
  vi_xs : Forall (fun x => 1 <= x <= 30) xs;
  vi_ys : Forall (fun y => 1 <= y <= 30) ys;
  vi_zs : Forall (fun z => 1 <= z <= 30) zs;
}.

(* The answer is s when the player to move wins the starting position, its
   opponent when the player to move loses it. *)
Definition winner_spec (s : player) (xs ys zs : list N) (o : player) : Prop :=
  (o = s <-> wins (initial xs ys zs)) /\
  (o = opponent s <-> loses (initial xs ys zs)).

Program winner : player -> array uint -> array uint -> array uint -> player.

Specification winner_correct :
  forall (s : player) (xs ys zs : list N)
         (s' : player) (a b c : array uint),
  valid_input xs ys zs -> repr s' s -> repr a xs -> repr b ys -> repr c zs ->
  exists o : player, repr (winner s' a b c) o /\ winner_spec s xs ys zs o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
