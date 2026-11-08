(** * Knigs of the Forest *)

(** ** Description *)

(** Process annual arrivals into a competition where the strongest active
    participant wins and leaves each year. Determine when a designated
    participant wins, or whether the known arrivals are insufficient to
    tell.

    [@kattis knigsoftheforest]
    - Difficulty: 3.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Pool size and observed year count from 1 to $10^{5}$.
    - Entry years span 2011 through 2011 + year count - 1.
    - Distinct strengths from 0 to $2^{31}$ - 1; a full pool enters initially
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The moose are numbered: moose 0 is Karl-Algtav, moose i +
    1 the i-th of the other moose, so their years are karl_year ::
    other_years and their strengths karl_strength ::
    other_strengths. The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry of moose in the column. *)
Definition entry (column : list N) (moose : N) : N :=
  nth (N.to_nat moose) column 0.

(** year is one of the year_count years for which the data are
    sufficient. *)
Definition data_year (year_count year : N) : Prop :=
  2011 <= year <= 2011 + year_count - 1.

(** Given the winners winner of the earlier years, moose competes in
    year: it exists, has entered by year, and has not won in any
    year 2011 .. year - 1. *)
Definition contender (all_years : list N)
  (winner : N -> N) (year moose : N)
    : Prop :=
  moose < len all_years /\ entry all_years moose <= year /\
  forall year', 2011 <= year' < year ->
    winner year' <> moose.

(** winner gives the winner of every data year: a contender of that
    year, at least as strong as every contender of that year. *)
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
    The output is the year when the designated participant wins, or None if that
    participant does not win within the years determined by the input. *)
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

(** ** Interface *)

(** Process annual arrivals into a competition where the strongest active participant wins
    and leaves each year. Determine when a designated participant wins, or whether the
    known arrivals are insufficient to tell.
    - Input [pool_size]:
    - Input [year_count]:
    - Input [karl_year]:
    - Input [karl_strength]:
    - Input [other_years]:
    - Input [other_strengths]:
    - Output [output]: *)
Program knigsoftheforest :
  uint -> uint -> uint -> uint -> array uint ->
    array uint -> option uint.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
