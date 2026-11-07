(** * Arbitrage? *)

(** ** Description *)

(** Decide whether a cycle of currency exchanges can increase the starting
    amount, using the given exact exchange rates.

    [@kattis arbitrage]
    - Difficulty: 3.2

    **Kattis Bounds**
    - 1 to 200 currencies; at most C * (C - 1) exchange rates.
    - Each rate exchanges between 1 and 100 units of each of two distinct
      currencies. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
2
CZK EUR
2
CZK EUR 25:1
EUR CZK 1:25
2
GBP USD
2
USD GBP 8:5
GBP USD 5:9
3
BON DEM CZK
3
DEM BON 1:6
BON CZK 1:5
DEM CZK 1:20
3
CZK EUR GBP
3
CZK EUR 24:1
EUR GBP 5:4
GBP CZK 1:30
3
CZK USD GBP
4
CZK USD 28:1
CZK GBP 31:1
GBP CZK 1:31
USD GBP 1:1
0
Output:
Ok
Arbitrage
Ok
Ok
Arbitrage
*)

(** ** [@hide] Environment *)

(* @function        arbitrage
   @signature       uint -> array uint -> array uint -> array uint -> array uint -> bool
   @math_signature  N -> list N -> list N -> list N -> list N -> bool
   @summary         One test case of "Arbitrage?": [currency_count]
                    currencies and the exchange rates k (pay paid_units_k
                    units of currency from_currencies_k, get got_units_k
                    units of currency to_currencies_k).  The answer is true
                    ("Arbitrage") exactly when some sequence of exchanges,
                    starting and ending in the same currency, turns a positive
                    amount into a strictly larger one, amounts computed exactly
                    over the rationals; false ("Ok") otherwise.
*)

From Stdlib Require Import ZArith NArith QArith List Uint63
  PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A currency is its 0-based position in the
  line of codes (the
   codes of one test case are different); a rate is the k-th
     entry of four
   parallel lists, the columns of the input line "src dst
     A:B":
   from_currencies, to_currencies, paid_units
     (A) and got_units (B). *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of l (0 beyond the end, never read
    there). *)
Definition get (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** Performing the exchanges exchanges in order leads
    from currency start to currency finish: each one is
    paid in the currency the previous one produced. *)
Fixpoint leads (from_currencies to_currencies : list N)
  (start finish : N)
    (exchanges : list N) : Prop :=
  match exchanges with
  | [] => start = finish
  | k :: rest =>
      get from_currencies k = start /\
      leads from_currencies to_currencies
        (get to_currencies k) finish rest
  end.

(** The amount held after the exchanges exchanges,
    starting from amount units: paying amount units at
    rate A:B gives amount * B / A units. *)
Fixpoint amount_after (paid_units got_units : list N)
  (exchanges : list N)
    (amount : Q) : Q :=
  match exchanges with
  | [] => amount
  | k :: rest =>
      amount_after paid_units got_units rest
        (amount * (inject_Z (Z.of_N (get got_units k)) /
                   inject_Z (Z.of_N (get paid_units k))))%Q
  end.

(** Some nonempty sequence of available exchanges, from
    a currency back to itself, ends with strictly more
    than a positive starting amount. *)
Definition profitable
  (from_currencies to_currencies paid_units got_units
    : list N) : Prop :=
  exists (currency : N) (exchanges : list N) (amount : Q),
    exchanges <> [] /\
    Forall (fun k => k < len from_currencies) exchanges /\
    leads from_currencies to_currencies currency currency
      exchanges /\
    (0 < amount)%Q /\
    (amount < amount_after paid_units got_units exchanges
      amount)%Q.

(** [@inside arbitrage_correct] The statement's bounds,
    for one test case. *)
Record valid_input (currency_count : N)
    (from_currencies to_currencies paid_units got_units :
      list N) : Prop := {
  (* one positive integer number C, 1 <= C <= 200, the
    number of currencies *)
  vi_c : 1 <= currency_count <= 200;
  (* R, 0 <= R <= C *
    (C - 1), the number of exchange rates; each rate line
     gives a first code, a second code, A_i and B_i *)
  vi_r : len from_currencies <= currency_count *
    (currency_count - 1);
  vi_dst_len : len to_currencies = len from_currencies;
  vi_a_len : len paid_units = len from_currencies;
  vi_b_len : len got_units = len from_currencies;
  (* each code of a rate is one of the C currency codes of
    the test case *)
  vi_src : Forall
    (fun currency => currency < currency_count)
    from_currencies;
  vi_dst : Forall
    (fun currency => currency < currency_count)
    to_currencies;
  (* the two currencies are different *)
  vi_diff : forall k, k < len from_currencies ->
    get from_currencies k <> get to_currencies k;
  (* 1 <= A_i, B_i <= 100 *)
  vi_a : Forall (fun units => 1 <= units <= 100) paid_units;
  vi_b : Forall (fun units => 1 <= units <= 100) got_units;
}.

(** ** Correctness *)

(** [@requirement] [@short must decide whether a
    profitable currency-exchange cycle exists.]
    "Arbitrage" (true) exactly when some exchange
    sequence gives a profit. *)
Definition arbitrage_spec (currency_count : N)
    (from_currencies to_currencies paid_units got_units :
      list N)
    (output : bool) : Prop :=
  match output with
  | true => profitable from_currencies to_currencies
    paid_units got_units
  | false => ~ profitable from_currencies to_currencies
    paid_units got_units
  end.

(** ** Interface *)

(** The machine-level interface.
    - Input [currency_count]:
    - Input [from_currencies]:
    - Input [to_currencies]:
    - Input [paid_units]:
    - Input [got_units]:
    - Output [output]: *)
Program arbitrage :
  uint -> array uint -> array uint -> array uint
    -> array uint -> bool.

(** ** Bridge *)

(** [@requirement arbitrage_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [arbitrage_spec]. *)
Specification arbitrage_correct :
  forall (currency_count : N)
         (from_currencies to_currencies paid_units got_units
           : list N)
         (currency_count_int : uint)
         (from_currencies_arr to_currencies_arr : array
           uint)
         (paid_units_arr got_units_arr : array uint),
  valid_input currency_count from_currencies to_currencies
    paid_units
    got_units ->
  repr currency_count_int currency_count ->
  repr from_currencies_arr from_currencies ->
  repr to_currencies_arr to_currencies ->
  repr paid_units_arr paid_units
    -> repr got_units_arr got_units ->
  exists output : bool,
    repr (arbitrage currency_count_int from_currencies_arr
      to_currencies_arr
            paid_units_arr got_units_arr) output /\
    arbitrage_spec currency_count from_currencies
      to_currencies paid_units
      got_units output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals
    rest on: the math side is not over R, but an
    accepted implementation proves through Stdlib's
    reals (decision of 2026-10-23). *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
