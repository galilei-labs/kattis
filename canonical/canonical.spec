(** * Canonical Coin Systems *)

(** ** Description *)

(** Decide whether repeatedly choosing the largest affordable coin always
    yields a minimum-size representation of every positive amount.

    [@kattis canonical]
    - Difficulty: 4.7
    - CPU time limit: 2 seconds
    - Memory limit: 2048 MB

    **Kattis Bounds**
    - 2 to 100 strictly increasing denominations.
    - The first denomination is 1; the largest is at most $10^{6}$. *)

(** ** Examples *)

(** - Input convention: Denomination count, followed by strictly increasing coin values starting with 1.
    - Output convention: canonical if greedy change is always optimal; non-canonical otherwise. *)
(* Input:
4
1 2 4 8
Output:
canonical
*)

(** ** [@hide] Environment *)

(* @function        canonical
   @signature       array uint -> bool
   @math_signature  list N -> bool
   @summary         [canonical denominations] takes a coin system given as
                    its denominations in increasing order, the first being
                    1, and returns true exactly when the system is canonical:
                    no positive amount has a minimum number of coins
                    strictly smaller than the number of coins the greedy
                    algorithm uses for it.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A coin system is the list of its
  denominations, c_1 first. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The denomination c_(k+1) (index k, from 0). *)
Definition coin (denominations : list N) (k : N) : N :=
  nth (N.to_nat k) denominations 0.

(** amount is the sum of exactly coin_count coins of
    denominations, each denomination usable any number
    of times. *)
Inductive sums_to (denominations : list N) : N -> N
  -> Prop :=
| sums_nil : sums_to denominations 0 0
| sums_cons : forall denomination amount coin_count,
    In denomination denominations ->
    sums_to denominations amount coin_count ->
    sums_to denominations (amount + denomination)
      (coin_count + 1).

(** coin_count is the smallest number of coins required
    to dispense exactly amount. *)
Definition min_coins (denominations : list N)
  (amount coin_count : N)
  : Prop :=
  sums_to denominations amount coin_count /\
  forall coin_count', sums_to denominations amount
    coin_count' ->
    coin_count <= coin_count'.

(** denomination is a coin of the largest denomination
    that is at most amount. *)
Definition largest_le (denominations : list N)
  (amount denomination : N)
  : Prop :=
  In denomination denominations /\ denomination <= amount /\
  forall other, In other denominations -> other <= amount ->
    other <= denomination.

(** The greedy algorithm, repeatedly choosing a coin of
    the largest denomination at most the amount still
    owed until it reaches zero, dispenses amount with
    greedy_count coins. *)
Inductive greedy_uses (denominations : list N) : N -> N
  -> Prop :=
| greedy_nil : greedy_uses denominations 0 0
| greedy_step : forall amount denomination greedy_count,
    0 < amount
      -> largest_le denominations amount denomination ->
    greedy_uses denominations
      (amount - denomination) greedy_count ->
    greedy_uses denominations amount (greedy_count + 1).

(** A counterexample: a positive integer amount such
    that the minimum number of coins required to
    dispense exactly amount is less than the number of
    coins used by the greedy algorithm. *)
Definition counterexample (denominations : list N)
  (amount : N) : Prop :=
  0 < amount /\
  exists coin_count greedy_count,
    min_coins denominations amount coin_count /\
    greedy_uses denominations amount greedy_count /\
    coin_count < greedy_count.

(** [@inside canonical_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (denominations : list N) : Prop := {
  (* 2 <= n <= 100, the number of denominations *)
  vi_n : 2 <= len denominations <= 100;
  (* c_1 = 1 *)
  vi_first : coin denominations 0 = 1;
  (* c_1 < c_2 < ... < c_n *)
  vi_increasing : forall k, k + 1 < len denominations ->
    coin denominations k < coin denominations (k + 1);
  (* c_n <= 10^6
    (each denomination, the largest being c_n) *)
  vi_max : Forall
    (fun denomination => denomination <= 10 ^ 6)
    denominations;
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when greedy coin selection minimizes the number of coins
    for every positive amount. *)
Definition canonical_spec (denominations : list N)
  (output : bool)
  : Prop :=
  match output with
  | true =>
    forall amount, ~ counterexample denominations amount
  | false => ~
    forall amount, ~ counterexample denominations amount
  end.

(** ** Interface *)

(** Decide whether repeatedly choosing the largest affordable coin always yields a minimum-
    size representation of every positive amount.
    - Input [denominations]:
    - Output [output]: *)
Program canonical : array uint -> bool.

(** ** Bridge *)

(** [@requirement canonical_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [canonical_spec]. *)
Specification canonical_correct :
  forall (denominations : list N)
    (denominations_arr : array uint),
  valid_input denominations
    -> repr denominations_arr denominations ->
  exists output : bool,
    repr (canonical denominations_arr) output /\
    canonical_spec denominations output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
