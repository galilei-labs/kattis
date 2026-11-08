(** * Worst Weather Ever *)

(** ** Description *)

(** For each queried pair of years, test whether the later rainfall is no
    greater than the earlier rainfall and exceeds every intervening year's
    rainfall. Classify the claim as confirmed, impossible or still possible
    when records are missing.

    [@kattis worstweather]
    - Difficulty: 6.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 50,000 recorded years and 1 to 10,000 queries.
    - Years from -$10^{9}$ to $10^{9}$; recorded years are strictly
      increasing.
    - Rainfall from 1 to $10^{9}$; each query's first year precedes its
      second. *)

(** ** Examples *)

(** - Input convention: Per case: year-rainfall records followed by year-pair queries; zero record and query counts end input.
    - Output convention: true, false or maybe per query; a blank line separates cases. *)
(* Input:
4
2002 4920
2003 5901
2004 2832
2005 3890
2
2002 2005
2003 2005

3
1985 5782
1995 3048
2005 4890
2
1985 2005
2005 2015

0
0
Output:
false
true

maybe
maybe
*)

(** ** [@hide] Environment *)

(* @function        worstweather
   @signature       array sint -> array uint -> array sint -> array sint ->
                    array answer
   @math_signature  list Z -> list N -> list Z -> list Z -> list answer
   @summary         One test case: the known years (increasing) with their
                    rainfalls, and the statements "year record_years_k had
                    the most rain since year since_years_k".  Answer k is
                    Ans_true when every year from since_years_k to
                    record_years_k is known and the statement holds,
                    Ans_maybe when it is not true but some nonnegative
                    amounts of rain for the unknown years make it hold, and
                    Ans_false otherwise.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The three outputs "true", "maybe", "false", on both
    sides. *)
Inductive answer := Ans_true | Ans_maybe | Ans_false.
Instance repr_answer : Repr answer answer :=
  fun x i => x = i.

(* Math side. Years are signed (the statement allows
   negatives), amounts of rain are nonnegative; the known
   years and their rain, and the two years of the
   queries, come as parallel lists, one per column of the
   input. *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The element of index i of l (0-based). *)
Definition at_ {A} (l : list A) (default : A) (i : N) : A :=
  nth (N.to_nat i) l default.

(** There is information about year. *)
Definition known (years : list Z) (year : Z) : Prop :=
  In year years.

(** An [assignment] of an amount of rain to every year
    that agrees with the information: year years_i gets
    rainfalls_i, the others any nonnegative integer. *)
Definition assignment (years : list Z) (rainfalls : list N)
  (rain_of : Z -> N)
    : Prop :=
  forall i, (i < len years)%N -> rain_of (at_ years 0 i) =
    at_ rainfalls 0%N i.

(** "Year record_year had the most rain since year
    since_year" under the amounts rain_of: it rained at
    most as much in record_year as in since_year, and
    less than in record_year in every year strictly
    between them. *)
Definition most_rain_since (rain_of : Z -> N)
  (since_year record_year : Z)
    : Prop :=
  (rain_of record_year <= rain_of since_year)%N /\
  (forall year, since_year < year < record_year ->
     (rain_of year < rain_of record_year)%N).

(** The rainfall claim holds and every year in the inclusive interval has a recorded value. *)
Definition is_true (years : list Z) (rainfalls : list N)
    (since_year record_year : Z) : Prop :=
  (forall year, since_year <= year <= record_year -> known
    years year) /\
  (forall rain_of, assignment years rainfalls rain_of ->
     most_rain_since rain_of since_year record_year).

(** At least one assignment of missing rainfall values satisfies the claim. *)
Definition might_be_true (years : list Z)
  (rainfalls : list N)
    (since_year record_year : Z) : Prop :=
  exists rain_of, assignment years rainfalls rain_of /\
    most_rain_since rain_of since_year record_year.

(** verdict is the [answer] to "year record_year had the
    most rain since year since_year". *)
Definition answers (years : list Z) (rainfalls : list N)
    (since_year record_year : Z) (verdict : answer) : Prop
      :=
  (verdict = Ans_true <-> is_true years rainfalls since_year
    record_year) /\
  (verdict = Ans_maybe <->
     ~ is_true years rainfalls since_year record_year /\
     might_be_true years rainfalls since_year record_year)
       /\
  (verdict = Ans_false <->
     ~ might_be_true years rainfalls since_year
       record_year).

(** [@inside worstweather_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (years : list Z) (rainfalls : list N)
    (since_years record_years : list Z) : Prop := {
  (* 1 <= n <= 50 000, the number of years for which
     there is information (n = 0 is the terminator, not a
     test case) *)
  vi_n : (1 <= len years <= 50000)%N;
  (* the i-th of these n lines contains y_i and r_i *)
  vi_rs : len rainfalls = len years;
  (* -10^9 <= y_i <= 10^9 *)
  vi_years : Forall (fun year => - 10 ^ 9 <= year <= 10 ^ 9)
    years;
  (* 1 <= r_i <= 10^9 *)
  vi_rain : Forall (fun rain => 1 <= rain <= 10 ^ 9)%N
    rainfalls;
  (* you may assume that y_i < y_(i+1) for 1 <= i < n *)
  vi_increasing : forall i, (i + 1 < len years)%N ->
    at_ years 0 i < at_ years 0 (i + 1)%N;
  (* 1 <= m <= 10 000, the number of queries *)
  vi_m : (1 <= len since_years <= 10000)%N;
  (* each of the m lines contains two years Y and X *)
  vi_qx : len record_years = len since_years;
  (* -10^9 <= Y < X <= 10^9 *)
  vi_queries : forall k, (k < len since_years)%N ->
    - 10 ^ 9 <= at_ since_years 0 k /\
    at_ since_years 0 k < at_ record_years 0 k /\
    at_ record_years 0 k <= 10 ^ 9;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry classifies the rainfall claim as confirmed by complete records,
    contradicted by the records or possible given missing records. *)
Definition worstweather_spec
  (years : list Z )
  (rainfalls : list N )
  (since_years record_years : list Z )
  (output : list answer )
  : Prop :=
  len output = len since_years /\
  forall k, (k < len since_years)%N ->
    answers years rainfalls (at_ since_years 0 k) (at_
      record_years 0 k)
      (at_ output Ans_false k).

(** ** Interface *)

(** For each queried pair of years, test whether the later rainfall is no greater than the
    earlier rainfall and exceeds every intervening year's rainfall. Classify the claim
    as confirmed, impossible or still possible when records are missing.
    - Input [years]:
    - Input [rainfalls]:
    - Input [since_years]:
    - Input [record_years]:
    - Output [output]: *)
Program worstweather :
  array sint -> array uint -> array sint -> array sint ->
    array answer.

(** ** Bridge *)

(** [@requirement worstweather_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [worstweather_spec]. *)
Specification worstweather_correct :
  forall (years : list Z) (rainfalls : list N)
         (since_years record_years : list Z)
         (years_arr : array sint ) (rainfalls_arr :
           array uint )
         (since_years_arr record_years_arr : array sint),
  valid_input years rainfalls since_years record_years ->
  repr years_arr years -> repr rainfalls_arr rainfalls ->
  repr since_years_arr since_years -> repr record_years_arr
    record_years ->
  exists output : list answer,
    repr (worstweather years_arr rainfalls_arr
      since_years_arr
            record_years_arr) output /\
    worstweather_spec years rainfalls since_years
      record_years output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
