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
    - Recorded year count: $1 \le n \le 5 \times 10^{4}$ and Query count: $1 \le q \le 10^{4}$.
    - Years: $-10^{9} \le y \le 10^{9}$; recorded years are strictly
      increasing.
    - Rainfall: $1 \le r \le 10^{9}$; each query's first year precedes its
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
                    It runs in at most c1 * (n + m + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of known years and m of queries (the range-maximum
                    structure, then binary searches and lookups per query),
                    for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** A rainfall verdict: confirmed by complete records, contradicted by the records,
    or still possible given missing records. *)
Inductive answer := Ans_true | Ans_maybe | Ans_false.

(** [@hide] Machine and mathematical answers represent themselves. *)
Instance repr_answer : Repr answer answer :=
  fun x i => x = i.

(** [@hide] The cost translation of [answer], for the bound below. *)
Elpi complexity answer.

(* Math side. Years are signed (the statement allows
   negatives), amounts of rain are nonnegative; the known
   years and their rain, and the two years of the
   queries, come as parallel lists, one per column of the
   input. *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [i] in [l], or [default] beyond the end. *)
Definition at_ {A} (l : list A) (default : A) (i : N) : A :=
  nth (N.to_nat i) l default.

(** The input records rainfall for [year]. *)
Definition known (years : list Z) (year : Z) : Prop :=
  In year years.

(** [rain_of] assigns nonnegative integer rainfall to every year and agrees with all
    supplied records. *)
Definition assignment (years : list Z) (rainfalls : list N)
  (rain_of : Z -> N)
    : Prop :=
  forall i, (i < len years)%N -> rain_of (at_ years 0 i) =
    at_ rainfalls 0%N i.

(** Rainfall in [record_year] is no greater than in [since_year], and is strictly
    greater than in every intervening year, according to [rain_of]. *)
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

(** [verdict] classifies the rainfall claim for [since_year] and [record_year] as
    confirmed, contradicted, or still possible. *)
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
  (* 1 <= n <= 5 * 10^4, the number of years for which
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
  (* 1 <= m <= 10^4, the number of queries *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O((n+q+1)\log(n+2))$ steps, where $n$ is the number of recorded years and $q$ the number of queries. *)
Definition worstweather_time_spec (c1 c2 n_years n_since_years steps : nat) : Prop :=
  (steps <= c1 * ((n_years + n_since_years + 1) * (Nat.log2 (n_years) + 1)) + c2)%nat.

(** ** Interface *)

(** For each queried pair of years, test whether the later rainfall is no greater than the
    earlier rainfall and exceeds every intervening year's rainfall. Classify the claim
    as confirmed, impossible or still possible when records are missing.
    - Input [years]: Recorded years in strictly increasing order.
    - Input [rainfalls]: Rainfall recorded for each corresponding year.
    - Input [since_years]: Earlier endpoint of each year-range query.
    - Input [record_years]: Later endpoint of each year-range query.
    - Output [output]: Each output entry classifies the rainfall claim as confirmed by complete records, contradicted by the records or possible given missing records. *)
Program worstweather :
  array sint -> array uint -> array sint -> array sint ->
    array answer.

(** [@example worstweather]
    - Sample: 1
    - Case: 1
    - Input [years]: [2002; 2003; 2004; 2005]%Z
    - Input [rainfalls]: [4920; 5901; 2832; 3890]
    - Input [since_years]: [2002; 2003]%Z
    - Input [record_years]: [2005; 2005]%Z
    - Output [output]: [Ans_false; Ans_true]
*)

(** [@example worstweather]
    - Sample: 1
    - Case: 2
    - Input [years]: [1985; 1995; 2005]%Z
    - Input [rainfalls]: [5782; 3048; 4890]
    - Input [since_years]: [1985; 2005]%Z
    - Input [record_years]: [2005; 2015]%Z
    - Output [output]: [Ans_maybe; Ans_maybe]
*)

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

(** ** Complexity *)

(** [@hide] [worstweather_cost] is the cost translation of [worstweather] (the judge
    recomputes it and compares) ... *)
Complexity worstweather_cost for worstweather.

(** [@fold complexity bound] ... and runs in at most c1 * (n + m + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of known years and m of queries (the range-maximum structure, then binary searches and lookups per query), for two constants
    quantified before the inputs, on every valid input. [@requirement worstweather_time_spec] *)
Specification worstweather_time : exists c1 c2 : nat,
  forall (years : list Z) (rainfalls : list N)
  (since_years record_years : list Z)
  (years_arr : array sint ) (rainfalls_arr :
  array uint )
  (since_years_arr record_years_arr : array sint),
  valid_input years rainfalls since_years record_years ->
  repr years_arr years -> repr rainfalls_arr rainfalls ->
  repr since_years_arr since_years -> repr record_years_arr
  record_years ->
  worstweather_time_spec c1 c2 (size years_arr) (size since_years_arr) (cost4 worstweather_cost years_arr rainfalls_arr since_years_arr record_years_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
