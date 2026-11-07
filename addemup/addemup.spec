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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A card is the positive number printed on it. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The digit digit, shown upside down, reads rotated (the font of the
   statement). *)
Definition rotates (digit rotated : N) : Prop :=
  In (digit, rotated) [(0, 0); (1, 1); (2, 2); (5, 5); (6, 9); (8, 8); (9, 6)].

(* The number written by the digits digits, most significant first. *)
Definition decimal (digits : list N) : N :=
  fold_left (fun acc digit => 10 * acc + digit) digits 0.

(* digits is the decimal writing of number: digits, no leading zero. *)
Definition writes (digits : list N) (number : N) : Prop :=
  digits <> [] /\ Forall (fun digit => digit <= 9) digits /\
  hd 0 digits <> 0 /\ decimal digits = number.

(* Turned upside down, the card card shows the number shown: its digits in
   reverse order, each rotated.  Leading zeros of the result are read as
   in any decimal number (the card 10 shows 1). *)
Definition upside_down (card shown : N) : Prop :=
  exists digits rotated_digits,
    writes digits card /\ Forall2 rotates (rev digits) rotated_digits /\
    decimal rotated_digits = shown.

(* The card card can show the number shown, either way up. *)
Definition shows (card shown : N) : Prop :=
  shown = card \/ upside_down card shown.

(* Two different cards can show numbers adding up to desired_sum. *)
Definition winnable (desired_sum : N) (cards : list N) : Prop :=
  exists i j shown_i shown_j,
    i < len cards /\ j < len cards /\ i <> j /\
    shows (nth (N.to_nat i) cards 0) shown_i /\
    shows (nth (N.to_nat j) cards 0) shown_j /\
    shown_i + shown_j = desired_sum.

(* The statement's bounds. *)
Record valid_input (desired_sum : N) (cards : list N) : Prop := {
  (* 1 <= n <= 100 000, n the number of cards *)
  vi_n : 1 <= len cards <= 100000;
  (* n integers between 1 and 100 000 000 inclusive *)
  vi_cards : Forall (fun card => 1 <= card <= 100000000) cards;
  (* 2 <= s <= 200 000 000, s the desired sum *)
  vi_s : 2 <= desired_sum <= 200000000;
}.

(* YES (true) exactly when the game can be won. *)
Definition addemup_spec (desired_sum : N) (cards : list N) (output : bool)
    : Prop :=
  match output with
  | true => winnable desired_sum cards
  | false => ~ winnable desired_sum cards
  end.

Program addemup : uint -> array uint -> bool.

Specification addemup_correct :
  forall (desired_sum : N) (cards : list N)
         (desired_sum_int : uint) (cards_arr : array uint),
  valid_input desired_sum cards ->
  repr desired_sum_int desired_sum -> repr cards_arr cards ->
  exists output : bool,
    repr (addemup desired_sum_int cards_arr) output /\
    addemup_spec desired_sum cards output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
