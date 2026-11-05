(* @function        addemup
   @signature       uint -> array uint -> bool
   @math_signature  N -> list N -> bool
   @summary         [addemup s cards] is true exactly when two different
                    cards (two distinct positions of cards) can be chosen,
                    each shown either way up, so that the two numbers shown
                    add up to s.  A card can be turned only if every one of
                    its digits still reads as a digit upside down: 0, 1, 2,
                    5, 8 read as themselves, 6 and 9 as each other, 3, 4, 7
                    not at all; the digits then read in reverse order.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A card is the positive number printed on it. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The digit d, shown upside down, reads e (the font of the statement). *)
Definition rotates (d e : N) : Prop :=
  In (d, e) [(0, 0); (1, 1); (2, 2); (5, 5); (6, 9); (8, 8); (9, 6)].

(* The number written by the digits ds, most significant first. *)
Definition decimal (ds : list N) : N :=
  fold_left (fun acc d => 10 * acc + d) ds 0.

(* ds is the decimal writing of x: digits, no leading zero. *)
Definition writes (ds : list N) (x : N) : Prop :=
  ds <> [] /\ Forall (fun d => d <= 9) ds /\ hd 0 ds <> 0 /\ decimal ds = x.

(* Turned upside down, the card x shows the number v: its digits in
   reverse order, each rotated.  Leading zeros of the result are read as
   in any decimal number (the card 10 shows 1). *)
Definition upside_down (x v : N) : Prop :=
  exists ds es, writes ds x /\ Forall2 rotates (rev ds) es /\ decimal es = v.

(* The card x can show the number v, either way up. *)
Definition shows (x v : N) : Prop := v = x \/ upside_down x v.

(* Two different cards can show numbers adding up to s. *)
Definition winnable (s : N) (cards : list N) : Prop :=
  exists i j vi vj,
    i < len cards /\ j < len cards /\ i <> j /\
    shows (nth (N.to_nat i) cards 0) vi /\
    shows (nth (N.to_nat j) cards 0) vj /\
    vi + vj = s.

(* The statement's bounds. *)
Record valid_input (s : N) (cards : list N) : Prop := {
  (* 1 <= n <= 100 000, n the number of cards *)
  vi_n : 1 <= len cards <= 100000;
  (* n integers between 1 and 100 000 000 inclusive *)
  vi_cards : Forall (fun c => 1 <= c <= 100000000) cards;
  (* 2 <= s <= 200 000 000 *)
  vi_s : 2 <= s <= 200000000;
}.

(* YES (true) exactly when the game can be won. *)
Definition addemup_spec (s : N) (cards : list N) (b : bool) : Prop :=
  b = true <-> winnable s cards.

Program addemup : uint -> array uint -> bool.

Specification addemup_correct :
  forall (s : N) (cards : list N) (x : uint) (y : array uint),
  valid_input s cards -> repr x s -> repr y cards ->
  exists b : bool, repr (addemup x y) b /\ addemup_spec s cards b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
