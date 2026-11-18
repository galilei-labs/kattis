(** * Knigs of the Forest *)

(** ** Description *)

(** A moose tribe holds an annual tournament. The strongest competing moose
    wins and permanently leaves; a newcomer replaces the winner for the next
    tournament, keeping the pool size constant. Karl wants to know when he
    will win. Given his entry year and strength, together with the other
    moose's strengths and entry years, determine his winning year. If he
    does not win during the years covered by the supplied arrivals, report
    that the information is insufficient; this does not mean he never wins.

    [@kattis knigsoftheforest]
    - Difficulty: 3.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Pool size and observed year count: $1 \le k, T \le 10^{5}$.
    - Entry years $y$ satisfy $2011 \le y \le 2011 + T - 1$, where $T$ is the year count.
    - Distinct strengths: $0 \le p_i \le 2^{31} - 1$; a full pool enters initially
      and one new participant enters each subsequent year. *)

(** ** Examples *)

(** - Input convention: Pool size and year count, then entry-year/strength pairs with the designated participant first.
    - Output convention: The designated participant's winning year, or unknown. *)
(* Input:
2 4
2013 2
2011 1
2011 3
2014 4
2012 6
Output:
2013
*)

(** ** [@hide] Environment *)
(* @function        knigsoftheforest
   @signature       uint -> uint -> uint -> uint -> array uint -> array uint
                    -> option uint
   @math_signature  N -> N -> N -> N -> list N -> list N -> option N
   @summary         [knigsoftheforest pool_size year_count karl_year
                    karl_strength other_years other_strengths]: Karl-Algtav
                    enters the tournament in year karl_year with strength
                    karl_strength, the other moose in years other_years with
                    strengths other_strengths (parallel lists).  Every year
                    from 2011 on, the strongest moose that has entered and
                    not yet won wins and leaves.  The result is Some year
                    when Karl wins in that year, one of the year_count years
                    2011 .. 2011 + year_count - 1 the data cover, and None
                    ("unknown") otherwise.
                    It runs in at most c1 * (n + k + y + 1) * (log2 k + 1) +
                    c2 steps of the cost model on a valid input, n the
                    number of other moose, k the pool size and y the number
                    of years (one heap extraction per year and one insertion
                    per newcomer, on a heap of at most k moose), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry for [moose] in the supplied data column. *)
Definition entry (column : list N) (moose : N) : N :=
  nth (N.to_nat moose) column 0.

(** [year] is one of the [year_count] years for which the data are sufficient. *)
Definition data_year (year_count year : N) : Prop :=
  2011 <= year <= 2011 + year_count - 1.

(** [moose] has entered by [year] and has not won in any earlier year, according to
    [winner]. *)
Definition contender (all_years : list N)
  (winner : N -> N) (year moose : N)
    : Prop :=
  moose < len all_years /\ entry all_years moose <= year /\
  forall year', 2011 <= year' < year ->
    winner year' <> moose.

(** [winner] selects, for each year covered by the data, a competing moose at least
    as strong as every other contender. *)
Definition schedule (year_count : N)
  (all_years all_strengths : list N)
    (winner : N -> N) : Prop :=
  forall year, data_year year_count year ->
    contender all_years winner year (winner year) /\
    forall moose, contender all_years winner year moose ->
      entry all_strengths moose <= entry all_strengths
        (winner year).

(** [@inside knigsoftheforest_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (pool_size year_count karl_year karl_strength : N)
    (other_years other_strengths : list N) : Prop := {
  (* 1 <= k <= 10^5, the size of the tournament pool *)
  vi_k : 1 <= pool_size <= 10 ^ 5;
  (* 1 <= n <= 10^5, the number of years with sufficient
     information *)
  vi_n : 1 <= year_count <= 10 ^ 5;
  (* Karl-Algtav: 2011 <= y <= 2011 + n - 1 *)
  vi_y : 2011 <= karl_year <= 2011 + year_count - 1;
  (* Karl-Algtav: 0 <= p <= 2^31 - 1 *)
  vi_p : karl_strength <= 2 ^ 31 - 1;
  (* then follow n + k - 2 lines describing each of the
     other moose *)
  vi_ys_len : len other_years = year_count + pool_size - 2;
  vi_ps_len : len other_strengths = year_count + pool_size -
    2;
  (* in the same format as for Karl-Algtav *)
  vi_ys : Forall (fun year => 2011 <= year <= 2011 +
    year_count - 1)
            other_years;
  vi_ps : Forall (fun strength => strength <= 2 ^ 31 - 1)
    other_strengths;
  (* exactly k of the moose will have 2011 as their year
     of entry *)
  vi_pool : len (filter (N.eqb 2011) (karl_year ::
    other_years)) = pool_size;
  (* the remaining n - 1 moose will have unique years of
     entry *)
  vi_newcomers : NoDup (filter (fun year => negb (year =?
    2011))
            (karl_year :: other_years));
  (* the strength of each moose is unique *)
  vi_strengths : NoDup (karl_strength :: other_strengths);
}.

(** ** Correctness *)

(** [@requirement]
    The output is the year Karl wins the moose tournament, or [None] if he
    does not win during the years covered by the known arrivals. *)
Definition knigsoftheforest_spec
    (pool_size year_count karl_year karl_strength : N)
    (other_years other_strengths : list N) (output : option
      N) : Prop :=
  (exists winner, schedule year_count (karl_year ::
    other_years)
            (karl_strength :: other_strengths)
            winner) /\
  forall winner, schedule year_count (karl_year ::
    other_years)
                   (karl_strength :: other_strengths) winner
            ->
    forall year, output = Some year <->
      data_year year_count year /\ winner year = 0.

(** ** Complexity *)

(** [@requirement] Runs in $O((m+k+y+1)\log(k+2))$ steps, where $m$ is the number of other moose, $k$ the pool size, and $y$ the number of years. *)
Definition knigsoftheforest_time_spec (c1 c2 n_other_years n_pool_size n_year_count steps : nat) : Prop :=
  (steps <= c1 * ((n_other_years + n_pool_size + n_year_count + 1) * (Nat.log2 (n_pool_size) + 1)) + c2)%nat.

(** ** Interface *)

(** Determine when Karl becomes the winning moose, as each year's strongest
    contender wins and leaves the tournament pool.
    - Input [pool_size]: Number of moose competing each year.
    - Input [year_count]: Number of tournament years covered by the known arrivals, starting in 2011.
    - Input [karl_year]: Year Karl enters the tournament pool.
    - Input [karl_strength]: Karl's strength.
    - Input [other_years]: Entry years of the other moose.
    - Input [other_strengths]: Strengths of the corresponding moose.
    - Output [output]: [Some] year when Karl wins, or [None] if he does not win within the known years and later results cannot be determined. *)
Program knigsoftheforest :
  uint -> uint -> uint -> uint -> array uint ->
    array uint -> option uint.

(** [@example knigsoftheforest]
    - Sample: 1
    - Input [pool_size]: 2
    - Input [year_count]: 4
    - Input [karl_year]: 2013
    - Input [karl_strength]: 2
    - Input [other_years]: [2011; 2011; 2014; 2012]
    - Input [other_strengths]: [1; 3; 4; 6]
    - Output [output]: Some 2013
*)

(** ** Bridge *)

(** [@requirement knigsoftheforest_spec] [@fold full correctness
    statement] On valid represented inputs, [knigsoftheforest]
    returns a represented output satisfying [knigsoftheforest_spec]. *)
Specification knigsoftheforest_correct :
  forall (pool_size year_count karl_year karl_strength : N)
         (other_years other_strengths : list N)
         (pool_size_int year_count_int karl_year_int
           karl_strength_int : uint)
         (other_years_arr other_strengths_arr : array uint),
  valid_input pool_size year_count karl_year karl_strength
    other_years
    other_strengths ->
  repr pool_size_int pool_size ->
    repr year_count_int year_count ->
  repr karl_year_int karl_year ->
    repr karl_strength_int karl_strength ->
  repr other_years_arr other_years ->
  repr other_strengths_arr other_strengths ->
  exists output : option N,
    repr (knigsoftheforest pool_size_int year_count_int
      karl_year_int
            karl_strength_int other_years_arr
              other_strengths_arr) output /\
    knigsoftheforest_spec pool_size year_count karl_year
      karl_strength
      other_years other_strengths output.

(** ** Complexity *)

(** [@hide] [knigsoftheforest_cost] is the cost translation of [knigsoftheforest] (the judge
    recomputes it and compares) ... *)
Complexity knigsoftheforest_cost for knigsoftheforest.

(** [@fold complexity bound] ... and runs in at most c1 * (n + k + y + 1) * (log2 k + 1) + c2 steps of the cost model on a valid input, n the number of other moose, k the pool size and y the number of years (one heap extraction per year and one insertion per newcomer, on a heap of at most k moose), for two constants
    quantified before the inputs, on every valid input. [@requirement knigsoftheforest_time_spec] *)
Specification knigsoftheforest_time : exists c1 c2 : nat,
  forall (pool_size year_count karl_year karl_strength : N)
  (other_years other_strengths : list N)
  (pool_size_int year_count_int karl_year_int
  karl_strength_int : uint)
  (other_years_arr other_strengths_arr : array uint),
  valid_input pool_size year_count karl_year karl_strength
  other_years
  other_strengths ->
  repr pool_size_int pool_size ->
  repr year_count_int year_count ->
  repr karl_year_int karl_year ->
  repr karl_strength_int karl_strength ->
  repr other_years_arr other_years ->
  repr other_strengths_arr other_strengths ->
  knigsoftheforest_time_spec c1 c2 (size other_years_arr) (size pool_size_int) (size year_count_int) (cost6 knigsoftheforest_cost pool_size_int year_count_int karl_year_int karl_strength_int other_years_arr other_strengths_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
