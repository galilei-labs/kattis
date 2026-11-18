(** * Add 'Em Up! *)

(** ** Description *)

(** Decide whether two distinct numbered cards can sum to a target,
    optionally rotating either card by 180 degrees. Rotation reverses the
    digits, swaps 6 and 9, preserves 0, 1, 2, 5 and 8, and is invalid for 3,
    4 or 7.

    [@kattis addemup]
    - Difficulty: 5.5
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Card count: $1 \le n \le 10^{5}$; values: $1 \le a_i \le 10^{8}$.
    - Target sum: $2 \le s \le 2 \times 10^{8}$. *)

(** ** Examples *)

(** - Input convention: Card count and target sum, followed by the card values.
    - Output convention: YES if two cards can produce the target sum; NO otherwise. *)
(* Input:
3 66
15 21 22
Output:
NO
*)

(** ** [@hide] Environment *)

(* @function        addemup
   @signature       uint -> array uint -> bool
   @math_signature  N -> list N -> bool
   @summary         [addemup desired_sum cards] is true exactly when two
                    different cards (two distinct positions of cards) can be
                    chosen, each shown either way up, so that the two
                    numbers shown add up to desired_sum.  A card can be
                    turned only if every one of its digits still reads as a
                    digit upside down: 0, 1, 2, 5, 8 read as themselves, 6
                    and 9 as each other, 3, 4, 7 not at all; the digits then
                    read in reverse order.
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of cards (the sort of the readings and one binary search
                    per reading; the digits of a card are a bounded number),
                    for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A card is the positive number printed on it.
  *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The digit [digit] becomes [rotated] under the permitted 180-degree rotation. *)
Definition rotates (digit rotated : N) : Prop :=
  In (digit, rotated) [(0, 0); (1, 1); (2, 2); (5, 5);
    (6, 9); (8, 8); (9, 6)].

(** Read [digits] from left to right, extending the decimal prefix [acc]. *)
Fixpoint decimal_from (digits : list N) (acc : N) : N :=
  match digits with
  | [] => acc
  | digit :: rest => decimal_from rest (10 * acc + digit)
  end.

(** The integer represented by [digits], listed most significant first. *)
Definition decimal (digits : list N) : N :=
  decimal_from digits 0.

(** [digits] is a nonempty decimal representation of [number], with no leading zero. *)
Definition writes (digits : list N) (number : N) : Prop :=
  digits <> [] /\ Forall (fun digit => digit <= 9) digits /\
  hd 0 digits <> 0 /\ decimal digits = number.

(** Rotating [card] by 180 degrees yields [shown]: reverse the digits and rotate
    each one. Leading zeros in the result do not affect its value; for example,
    rotating 10 yields 1. *)
Definition upside_down (card shown : N) : Prop :=
  exists digits rotated_digits,
    writes digits card /\ Forall2 rotates
      (rev digits) rotated_digits /\
    decimal rotated_digits = shown.

(** [card] can display [shown], either upright or after a permitted 180-degree
    rotation. *)
Definition shows (card shown : N) : Prop :=
  shown = card \/ upside_down card shown.

(** Two distinct input cards can display values whose sum is [desired_sum]. *)
Definition winnable (desired_sum : N)
  (cards : list N) : Prop :=
  exists i j shown_i shown_j,
    i < len cards /\ j < len cards /\ i <> j /\
    shows (nth (N.to_nat i) cards 0) shown_i /\
    shows (nth (N.to_nat j) cards 0) shown_j /\
    shown_i + shown_j = desired_sum.

(** [@inside addemup_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (desired_sum : N)
  (cards : list N) : Prop := {
  (* 1 <= n <= 10^5, n the number of cards *)
  vi_n : 1 <= len cards <= 100000;
  (* n integers between 1 and 10^8 inclusive *)
  vi_cards : Forall
    (fun card => 1 <= card <= 100000000) cards;
  (* 2 <= s <= 2 * 10^8, s the desired sum *)
  vi_s : 2 <= desired_sum <= 200000000;
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when two distinct cards, each in an allowed orientation,
    sum to the target. *)
Definition addemup_spec (desired_sum : N) (cards : list N)
  (output : bool)
    : Prop :=
  output = true <-> winnable desired_sum cards.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of cards. *)
Definition addemup_time_spec (c1 c2 n_cards steps : nat) : Prop :=
  (steps <= c1 * ((n_cards + 1) * (Nat.log2 (n_cards) + 1)) + c2)%nat.

(** ** Interface *)

(** Decide whether two distinct numbered cards can sum to a target, optionally rotating
    either card by 180 degrees. Rotation reverses the digits, swaps 6 and 9, preserves
    0, 1, 2, 5 and 8, and is invalid for 3, 4 or 7.
    - Input [desired_sum]: Required sum of two selected cards.
    - Input [cards]: Numbers printed on the cards, in input order.
    - Output [output]: The output is true exactly when two distinct cards, each in an allowed orientation, sum to the target. *)
Program addemup : uint -> array uint -> bool.

(** [@example addemup]
    - Sample: 1
    - Input [desired_sum]: 66
    - Input [cards]: [15; 21; 22]
    - Output [output]: false
*)

(** ** Bridge *)

(** [@requirement addemup_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [addemup_spec]. *)
Specification addemup_correct :
  forall (desired_sum : N) (cards : list N)
         (desired_sum_int : uint) (cards_arr : array uint),
  valid_input desired_sum cards ->
  repr desired_sum_int desired_sum -> repr cards_arr cards
    ->
  exists output : bool,
    repr (addemup desired_sum_int cards_arr) output /\
    addemup_spec desired_sum cards output.

(** ** Complexity *)

(** [@hide] [addemup_cost] is the cost translation of [addemup] (the judge
    recomputes it and compares) ... *)
Complexity addemup_cost for addemup.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of cards (the sort of the readings and one binary search per reading; the digits of a card are a bounded number), for two constants
    quantified before the inputs, on every valid input. [@requirement addemup_time_spec] *)
Specification addemup_time : exists c1 c2 : nat,
  forall (desired_sum : N) (cards : list N)
  (desired_sum_int : uint) (cards_arr : array uint),
  valid_input desired_sum cards ->
  repr desired_sum_int desired_sum -> repr cards_arr cards
  ->
  addemup_time_spec c1 c2 (size cards_arr) (cost2 addemup_cost desired_sum_int cards_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
