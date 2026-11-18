(** * Card Hand Sorting *)

(** ** Description *)

(** Reorder distinct playing cards so each suit is contiguous and its ranks
    are monotone in either direction. Find the fewest moves, where one move
    removes a card and reinserts it anywhere.

    [@kattis cardhand]
    - Difficulty: 4.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Distinct card count: $1 \le n \le 52$.
    - Thirteen ranks ($2$ through ace) and four suits. *)

(** ** Examples *)

(** - Input convention: Card count, followed by rank-suit codes such as 2s or Ah.
    - Output convention: A single integer giving the minimum number of moves. *)
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
                    It runs in at most c1 * (n + 1)^2 + c2 steps of the cost
                    model on a valid input, n the number of cards (one
                    longest-common-subsequence table per target order, a
                    fixed number of them), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Sorted.
From Stdlib Require Import String Ascii PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A card is the string of its two characters, a
  hand the list
   of its cards, left to right. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Card ranks in increasing order. *)
Definition rank_order : String.string := "23456789TJQKA".
(** The characters used for the four card suits. *)
Definition suit_chars : String.string := "shdc".

(** [character] occurs in [text]. *)
Definition char_in (character : ascii)
  (text : String.string) : Prop :=
  exists position, String.get position text = Some
    character.

(** The zero-based position of the first occurrence of [character] in [text]. *)
Fixpoint pos (character : ascii)
  (text : String.string) : nat :=
  match text with
  | EmptyString => 0
  | String first rest =>
      if Ascii.eqb first character then 0 else S
        (pos character rest)
  end.

(** The position of the card's first character in [rank_order]. *)
Definition rank (card : String.string) : nat :=
  match String.get 0 card with
  | Some rank_char => pos rank_char rank_order
  | None => 0
  end.

(** The suit character of [card], stored as its second character. *)
Definition suit (card : String.string) : ascii :=
  match String.get 1 card with
  | Some suit_char => suit_char
  | None => " "%char
  end.

(** Remove one card from [hand] and reinsert it at any position to obtain [hand']. *)
Definition move (hand hand' : list String.string) : Prop :=
  exists before card after before' after',
    hand = before ++ card :: after
      /\ before ++ after = before' ++ after' /\
    hand' = before' ++ card :: after'.

(** Exactly [move_count] card moves transform [hand] into [hand']. *)
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

(** The ranks of the cards of suit [suit_char], in hand order. *)
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

(** [@inside min_moves_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
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

(** [@requirement]
    The output is the minimum number of remove-and-reinsert moves required to group each
    suit contiguously with monotone ranks within each group. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O(n^2)$ steps, where $n$ is the number of cards in the hand. *)
Definition min_moves_time_spec (c1 c2 n_hand steps : nat) : Prop :=
  (steps <= c1 * ((n_hand + 1) * (n_hand + 1)) + c2)%nat.

(** ** Interface *)

(** Reorder distinct playing cards so each suit is contiguous and its ranks are monotone in
    either direction. Find the fewest moves, where one move removes a card and reinserts
    it anywhere.
    - Input [hand]: Cards in their original order, with rank and suit encoded for each card.
    - Output [output]: The output is the minimum number of remove-and-reinsert moves required to group each suit contiguously with monotone ranks within each group. *)
Program min_moves : array PrimString.string -> uint.

(** [@example min_moves]
    - Sample: 1
    - Input [hand]: ["2h"; "Th"; "8c"; "Qh"]%string
    - Output [output]: 1
*)

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

(** ** Complexity *)

(** [@hide] [min_moves_cost] is the cost translation of [min_moves] (the judge
    recomputes it and compares) ... *)
Complexity min_moves_cost for min_moves.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1)^2 + c2 steps of the cost model on a valid input, n the number of cards (one longest-common-subsequence table per target order, a fixed number of them), for two constants
    quantified before the inputs, on every valid input. [@requirement min_moves_time_spec] *)
Specification min_moves_time : exists c1 c2 : nat,
  forall (hand : list String.string)
  (hand_arr : array PrimString.string),
  valid_input hand -> repr hand_arr hand ->
  min_moves_time_spec c1 c2 (size hand_arr) (cost1 min_moves_cost hand_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
