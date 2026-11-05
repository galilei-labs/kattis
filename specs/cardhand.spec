(* @function        min_moves
   @signature       array PrimString.string -> uint
   @math_signature  list String.string -> N
   @summary         A hand of pairwise distinct cards, each a rank character
                    (2-9, T, J, Q, K, A, in increasing order) followed by a
                    suit character (s, h, d, c), is sorted when the cards of
                    each suit are contiguous and the ranks within each suit
                    are ascending or descending (the order of the suits and
                    the direction of each suit are free).  A move takes one
                    card out and reinserts it anywhere.  [min_moves h] is the
                    least number of moves that sorts the hand h.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Sorted.
From Stdlib Require Import String Ascii PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A card is the string of its two characters, a hand the list
   of its cards, left to right. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The ranks, in increasing order, and the suits. *)
Definition rank_order : String.string := "23456789TJQKA".
Definition suit_chars : String.string := "shdc".

(* Character ch occurs in s. *)
Definition char_in (ch : ascii) (s : String.string) : Prop :=
  exists k, String.get k s = Some ch.

(* The position of the first occurrence of ch in s. *)
Fixpoint pos (ch : ascii) (s : String.string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => if Ascii.eqb c ch then 0 else S (pos ch s')
  end.

(* The rank of a card: the position of its first character in rank_order. *)
Definition rank (c : String.string) : nat :=
  match String.get 0 c with Some r => pos r rank_order | None => 0 end.

(* The suit of a card: its second character. *)
Definition suit (c : String.string) : ascii :=
  match String.get 1 c with Some u => u | None => " "%char end.

(* One move: take card x out and put it back at any position. *)
Definition move (h h' : list String.string) : Prop :=
  exists a x b c d, h = a ++ x :: b /\ a ++ b = c ++ d /\ h' = c ++ x :: d.

(* h becomes h' after exactly k moves. *)
Fixpoint moves (k : nat) (h h' : list String.string) : Prop :=
  match k with
  | O => h = h'
  | S k => exists m, move h m /\ moves k m h'
  end.

(* The cards of each suit are contiguous. *)
Definition suits_grouped (h : list String.string) : Prop :=
  forall i j k x z, (i < j < k)%nat ->
    nth_error h i = Some x -> nth_error h k = Some z -> suit x = suit z ->
    exists y, nth_error h j = Some y /\ suit y = suit x.

(* The ranks of the cards of suit u, in hand order. *)
Definition ranks_of_suit (u : ascii) (h : list String.string) : list nat :=
  map rank (filter (fun c => Ascii.eqb (suit c) u) h).

(* Within each suit the ranks are ascending or descending. *)
Definition suits_monotone (h : list String.string) : Prop :=
  forall u, Sorted lt (ranks_of_suit u h) \/ Sorted gt (ranks_of_suit u h).

Definition sorted_hand (h : list String.string) : Prop :=
  suits_grouped h /\ suits_monotone h.

(* The statement's bounds. *)
Record valid_input (h : list String.string) : Prop := {
  (* an integer n (1 <= n <= 52), the number of cards in the hand *)
  vi_n : 1 <= len h <= 52;
  (* each card represented by two characters *)
  vi_two_chars : Forall (fun c => String.length c = 2%nat) h;
  (* the first character is a digit from 2 to 9 or one of T, J, Q, K, A *)
  vi_rank : Forall (fun c => exists r, String.get 0 c = Some r /\
                                       char_in r rank_order) h;
  (* the second character is from the set {s, h, d, c} *)
  vi_suit : Forall (fun c => exists u, String.get 1 c = Some u /\
                                       char_in u suit_chars) h;
  (* n pairwise distinct cards *)
  vi_distinct : NoDup h;
}.

(* m moves sort the hand, and no fewer do. *)
Definition min_moves_spec (h : list String.string) (m : N) : Prop :=
  (exists h', moves (N.to_nat m) h h' /\ sorted_hand h') /\
  (forall k h', moves k h h' -> sorted_hand h' -> m <= N.of_nat k).

Program min_moves : array PrimString.string -> uint.

Specification min_moves_correct :
  forall (h : list String.string) (x : array PrimString.string),
  valid_input h -> repr x h ->
  exists m : N, repr (min_moves x) m /\ min_moves_spec h m.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
