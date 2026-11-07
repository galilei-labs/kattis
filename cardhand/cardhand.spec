(** * Card Hand Sorting *)

(** ** Description *)

(** Reorder distinct playing cards so each suit is contiguous and its ranks
    are monotone in either direction. Find the fewest moves, where one move
    removes a card and reinserts it anywhere.

    [@kattis cardhand]
    - Difficulty: 4.4

    **Kattis Bounds**
    - 1 to 52 distinct cards.
    - Thirteen ranks (2 through ace) and four suits. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
4
2h Th 8c Qh
Output:
1
*)

(** ** [@hide] Environment *)

(* @function        min_moves
   @signature       array PrimString.string -> uint
   @math_signature  list String.string -> N
   @summary         A hand of pairwise distinct cards, each a rank character
                    (2-9, T, J, Q, K, A, in increasing order) followed by a
                    suit character (s, h, d, c), is sorted when the cards of
                    each suit are contiguous and the ranks within each suit
                    are ascending or descending (the order of the suits and
                    the direction of each suit are free).  A move takes one
                    card out and reinserts it anywhere.  [min_moves hand] is
                    the least number of moves that sorts the hand.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Sorted.
From Stdlib Require Import String Ascii PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A card is the string of its two characters, a
  hand the list
   of its cards, left to right. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The ranks, in increasing order, and the suits. *)
Definition rank_order : String.string := "23456789TJQKA".
(** The characters used for the four card suits. *)
Definition suit_chars : String.string := "shdc".

(** character occurs in text. *)
Definition char_in (character : ascii)
  (text : String.string) : Prop :=
  exists position, String.get position text = Some
    character.

(** The position of the first occurrence of character in
    text. *)
Fixpoint pos (character : ascii)
  (text : String.string) : nat :=
  match text with
  | EmptyString => 0
  | String first rest =>
      if Ascii.eqb first character then 0 else S
        (pos character rest)
  end.

(** The rank of a card: the position of its first
    character in rank_order. *)
Definition rank (card : String.string) : nat :=
  match String.get 0 card with
  | Some rank_char => pos rank_char rank_order
  | None => 0
  end.

(** The suit of a card: its second character. *)
Definition suit (card : String.string) : ascii :=
  match String.get 1 card with
  | Some suit_char => suit_char
  | None => " "%char
  end.

(** One move: take card out and put it back at any
    position. *)
Definition move (hand hand' : list String.string) : Prop :=
  exists before card after before' after',
    hand = before ++ card :: after
      /\ before ++ after = before' ++ after' /\
    hand' = before' ++ card :: after'.

(** hand becomes hand' after exactly move_count moves. *)
Fixpoint moves (move_count : nat)
  (hand hand' : list String.string) : Prop :=
  match move_count with
  | O => hand = hand'
  | S move_count' =>
      exists next_hand, move hand next_hand
        /\ moves move_count' next_hand hand'
  end.

(** The cards of each suit are contiguous. *)
Definition suits_grouped
  (hand : list String.string) : Prop :=
  forall i j k first last, (i < j < k)%nat ->
    nth_error hand i = Some first
      -> nth_error hand k = Some last ->
    suit first = suit last ->
    exists middle, nth_error hand j = Some middle
      /\ suit middle = suit first.

(** The ranks of the cards of suit suit_char, in hand
    order. *)
Definition ranks_of_suit (suit_char : ascii)
  (hand : list String.string)
  : list nat :=
  map rank (filter (fun card => Ascii.eqb
    (suit card) suit_char) hand).

(** Within each suit the ranks are ascending or
    descending. *)
Definition suits_monotone
  (hand : list String.string) : Prop :=
  forall suit_char,
    Sorted lt (ranks_of_suit suit_char hand) \/
    Sorted gt (ranks_of_suit suit_char hand).

(** Cards are grouped by suit, with ranks monotone
    within each suit. *)
Definition sorted_hand (hand : list String.string) : Prop :=
  suits_grouped hand /\ suits_monotone hand.

(** [@inside min_moves_correct] The statement's bounds. *)
Record valid_input (hand : list String.string) : Prop := {
  (* an integer n
    (1 <= n <= 52), the number of cards in the hand *)
  vi_n : 1 <= len hand <= 52;
  (* each card represented by two characters *)
  vi_two_chars : Forall
    (fun card => String.length card = 2%nat) hand;
  (* the first character is a digit from 2 to 9 or one of T,
    J, Q, K, A *)
  vi_rank : Forall (fun card =>
    exists rank_char, String.get 0 card =
                    Some rank_char
                      /\ char_in rank_char rank_order) hand;
  (* the second character is from the set {s, h, d, c} *)
  vi_suit : Forall (fun card =>
    exists suit_char, String.get 1 card =
                    Some suit_char
                      /\ char_in suit_char suit_chars) hand;
  (* n pairwise distinct cards *)
  vi_distinct : NoDup hand;
}.

(** ** Correctness *)

(** [@requirement] [@short must return the minimum moves
    needed to sort the hand.] output moves sort the
    hand, and no fewer do. *)
Definition min_moves_spec (hand : list String.string)
  (output : N)
  : Prop :=
  (exists final_hand,
     moves (N.to_nat output) hand final_hand
       /\ sorted_hand final_hand) /\
  (forall other_count final_hand',
     moves other_count hand final_hand'
       -> sorted_hand final_hand' ->
     output <= N.of_nat other_count).

(** ** Interface *)

(** The machine-level interface.
    - Input [hand]:
    - Output [output]: *)
Program min_moves : array PrimString.string -> uint.

(** ** Bridge *)

(** [@requirement min_moves_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [min_moves_spec]. *)
Specification min_moves_correct :
  forall (hand : list String.string)
    (hand_arr : array PrimString.string),
  valid_input hand -> repr hand_arr hand ->
  exists output : N,
    repr (min_moves hand_arr) output
      /\ min_moves_spec hand output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
