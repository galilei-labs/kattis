(** * Canonical Coin Systems *)

(** ** Description *)

(** Given the available coin values, decide whether the following greedy method
    always makes change using as few coins as possible: take the largest coin
    whose value does not exceed the remaining amount, subtract its value, and
    repeat until nothing remains. There is an unlimited supply of each coin.

    A coin system is called canonical if this method uses the fewest possible
    coins for every positive integer amount. For example, the values $1, 3, 4$
    are not canonical: for an amount of $6$, greedy selection takes $4+1+1$
    (three coins), whereas $3+3$ needs only two.

    [@kattis canonical]
    - Difficulty: 4.7
    - CPU time limit: 2 seconds
    - Memory limit: 2048 MB

    **Kattis Bounds**
    - Denomination count: $2 \le n \le 100$; denominations are strictly increasing.
    - The first denomination is $1$; the largest is at most $10^{6}$. *)

(** ** Examples *)

(** - Input convention: Denomination count, followed by strictly increasing coin values starting with 1.
    - Output convention: The function returns [true] if the coin system is canonical, and [false] otherwise. The Kattis text format prints these as "canonical" and "non-canonical", respectively. *)
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
                    It runs in at most c1 * (n + 1) * (c_n + 1) + c2 steps
                    of the cost model on a valid input, n the number of
                    denominations and c_n the largest ([max_size]; the
                    minimum-coin and greedy tables over the amounts below
                    twice c_n), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A coin system is the list of its
  denominations, c_1 first. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The denomination at zero-based index [k]. *)
Definition coin (denominations : list N) (k : N) : N :=
  nth (N.to_nat k) denominations 0.

(** [sums_to denominations amount coin_count] means that [amount] is the sum of
    exactly [coin_count] coins from [denominations], allowing any denomination
    to be used repeatedly. *)
Inductive sums_to (denominations : list N) : N -> N
  -> Prop :=
| sums_nil : sums_to denominations 0 0
| sums_cons : forall denomination amount coin_count,
    In denomination denominations ->
    sums_to denominations amount coin_count ->
    sums_to denominations (amount + denomination)
      (coin_count + 1).

(** [min_coins denominations amount coin_count] means that [amount] can be made
    using exactly [coin_count] coins with values from [denominations], and no
    smaller number of coins suffices. Each value may be used repeatedly. *)
Definition min_coins (denominations : list N)
  (amount coin_count : N)
  : Prop :=
  sums_to denominations amount coin_count /\
  forall coin_count', sums_to denominations amount
    coin_count' ->
    coin_count <= coin_count'.

(** [denomination] is the largest listed coin denomination not exceeding [amount]. *)
Definition largest_le (denominations : list N)
  (amount denomination : N)
  : Prop :=
  In denomination denominations /\ denomination <= amount /\
  forall other, In other denominations -> other <= amount ->
    other <= denomination.

(** [greedy_uses denominations amount greedy_count] means that repeatedly
    choosing the largest coin in [denominations] not exceeding the remaining
    amount dispenses [amount] using [greedy_count] coins. *)
Inductive greedy_uses (denominations : list N) : N -> N
  -> Prop :=
| greedy_nil : greedy_uses denominations 0 0
| greedy_step : forall amount denomination greedy_count,
    0 < amount
      -> largest_le denominations amount denomination ->
    greedy_uses denominations
      (amount - denomination) greedy_count ->
    greedy_uses denominations amount (greedy_count + 1).

(** [counterexample denominations amount] means that [amount] is positive and
    greedy selection using [denominations] takes more coins than necessary to
    make that same [amount]. *)
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
    [output] is [true] exactly when, for every positive integer amount, repeatedly
    taking the largest coin value in [denominations] that does not exceed the
    remaining amount uses the fewest possible coins. *)
Definition canonical_spec (denominations : list N)
  (output : bool)
  : Prop :=
  output = true <->
    forall amount, ~ counterexample denominations amount.

(** ** Complexity *)

(** [@requirement] Runs in $O((n+1)(M+1))$ steps, where $n$ is the number of denominations and $M$ the largest denomination. *)
Definition canonical_time_spec (c1 c2 n_denominations max_denominations steps : nat) : Prop :=
  (steps <= c1 * ((n_denominations + 1) * (max_denominations + 1)) + c2)%nat.

(** ** Interface *)

(** Decide whether the coin system [denominations] is canonical: taking the
    largest coin that fits the remaining amount, repeatedly, must use the fewest
    possible coins for every positive integer amount. Each coin value is
    available in unlimited quantity.
    - Input [denominations]: Available coin values in strictly increasing order, starting with one.
    - Output [output]: [true] if this greedy method always uses the fewest coins; [false] if some positive amount can be made with fewer coins than the method uses. *)
Program canonical : array uint -> bool.

(** [@example canonical]
    - Sample: 1
    - Input [denominations]: [1; 2; 4; 8]
    - Output [output]: true
*)

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

(** ** Complexity *)

(** [@hide] [canonical_cost] is the cost translation of [canonical] (the judge
    recomputes it and compares) ... *)
Complexity canonical_cost for canonical.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (c_n + 1) + c2 steps of the cost model on a valid input, n the number of denominations and c_n the largest ([max_size]; the minimum-coin and greedy tables over the amounts below twice c_n), for two constants
    quantified before the inputs, on every valid input. [@requirement canonical_time_spec] *)
Specification canonical_time : exists c1 c2 : nat,
  forall (denominations : list N)
  (denominations_arr : array uint),
  valid_input denominations
  -> repr denominations_arr denominations ->
  canonical_time_spec c1 c2 (size denominations_arr) (max_size denominations_arr) (cost1 canonical_cost denominations_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
