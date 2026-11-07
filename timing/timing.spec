(** * Timing *)

(** ** Description *)

(** Model transfers of strength between forts and find
    the least defended fort at the chosen attack time.

    [@kattis timing]
    - Difficulty: 3.5
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB *)

(** ** [@hide] Environment *)

(* @function        timing
   @signature       uint -> array float -> array uint -> array uint -> array float -> float
   @math_signature  N -> list R -> list N -> list N -> list R -> R
   @summary         One test case: [timing attack_time initial_strengths
                    link_sources link_targets link_fractions] takes N forts
                    holding the strengths initial_strengths and l links,
                    link j moving in every time unit the fraction
                    link_fractions_j of the units of fort link_sources_j (as
                    they were at the start of the unit) to fort
                    link_targets_j. After attack_time time units an attack
                    on a fort faces its own strength plus that of every
                    other fort joined to it by a link, in either direction;
                    the result is the lowest such value over the forts, with
                    an absolute or relative error less than 10^-6.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope bool_scope.
Open Scope N_scope.

(* Math side. The links are three parallel lists, one per
   column of the input lines "s t p" ; a strength or a
   fraction is the real its float denotes. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element, for k < [len] l (0 outside, never
    relied on). *)
Definition get_R (l : list R ) (k : N) : R := nth (N.to_nat
  k) l 0%R.
(** Get n. *)
Definition get_N (l : list N ) (k : N) : N := nth (N.to_nat
  k) l 0.

(** term 0 + term 1 + ... + term (count - 1). *)
Fixpoint sum_below (term : N -> R) (count : nat) : R :=
  match count with
  | O => 0%R
  | S count' =>
    (sum_below term count' + term (N.of_nat count'))%R
  end.

Section Galaxy.

  Variables (initial_strengths : list R)
    (link_sources link_targets : list N)
            (link_fractions : list R).

  (* One time unit, from the strengths current: fort
     receives link_fractions_j * current(link_sources_j)
     over every link j into it and loses link_fractions_j
     * current(fort) over every link j out of it (a link
     from fort to fort gives and takes the same amount). *)
  Definition step (current : N -> R) (fort : N) : R :=
    (current fort
     + sum_below (fun j => if get_N link_targets j =? fort
                           then get_R link_fractions j
                                * current
            (get_N link_sources j)
                           else 0)
                 (List.length link_sources)
     - sum_below (fun j => if get_N link_sources j =? fort
                           then get_R link_fractions j *
            current fort
                           else 0)
                 (List.length link_sources))%R.

  (* The strength of each fort after time time units. *)
  Fixpoint strength (time : nat) : N -> R :=
    match time with
    | O => get_R initial_strengths
    | S time => step (strength time)
    end.

  (* Forts fort and other are distinct and some link
     joins them, in either direction. *)
  Definition joined (fort other : N) : bool :=
    negb (fort =? other) &&
    existsb (fun j => (get_N link_sources j =? fort)
                      && (get_N link_targets j =? other)
                   || (get_N link_sources j =? other)
                      && (get_N link_targets j =? fort))
            (map N.of_nat (seq 0 (List.length
        link_sources)))
            .

  (* What an attack on fort faces after time time units:
     its own strength and that of every fort joined to
     it. *)
  Definition faced (time : nat) (fort : N) : R :=
    (strength time fort
     + sum_below (fun other => if joined fort other then
       strength time other
                               else 0)
                 (List.length initial_strengths))%R.

  (* The total fraction fort sends to other forts in one
     time unit. *)
  Definition outflow (fort : N) : R :=
    sum_below (fun j => if (get_N link_sources j =? fort)
                           && negb
            (get_N link_targets j =? fort)
                        then get_R link_fractions j else
            0%R)
              (List.length link_sources).

End Galaxy.

(** [@inside timing_correct] The statement's bounds, for
    one test case (1 <= T <= 10 test cases: one call per
    test case). *)
Record valid_input (attack_time : N)
  (initial_strengths : list R)
    (link_sources link_targets : list N)
      (link_fractions : list R)
  : Prop := {
  (* the number of enemy forts N (1 <= N <= 100) *)
  vi_N : 1 <= len initial_strengths <= 100;
  (* the number of links l (0 <= l <= (N-1)^2) *)
  vi_l : len link_sources <= (len initial_strengths - 1) ^
    2;
  (* the time from now when to attack t (0 <= t <= 5000) *)
  vi_t : attack_time <= 5000;
  (* l lines, each two integers s_j t_j and one double
     p_j *)
  vi_dst_len : len link_targets = len link_sources;
  vi_frac_len : len link_fractions = len link_sources;
  (* N doubles u_i (0 <= u_i <= 1000) *)
  vi_u : Forall (fun units => 0 <= units <= 1000)%R
    initial_strengths;
  (* s_j (0 <= s_j < N), t_j (0 <= t_j < N) *)
  vi_src : Forall
    (fun source => source < len initial_strengths)
             link_sources;
  vi_dst : Forall
    (fun target => target < len initial_strengths)
             link_targets;
  (* one double p_j (0 < p_j <= 1) *)
  vi_frac : Forall (fun fraction => 0 < fraction <= 1)%R
    link_fractions;
  (* "for each fort a fraction of the units is moved to
     other forts in each time unit": what leaves a fort
     is a fraction of its units, at most 1. The slack
     10^-9 is there because the decimals p_j are received
     as doubles, whose reals may sum to slightly more
     than 1 when the decimals sum to exactly 1 (fval 0.2
     + fval 0.8 = 1 + 5.6e-17; each double is within a
     relative 2^-53 of its decimal) *)
  vi_outflow : forall fort, fort < len initial_strengths ->
    (outflow link_sources link_targets link_fractions fort
       <= 1 + / 1000000000)%R;
}.

(** ** Correctness *)

(** [@requirement] [@short Model transfers of strength
    between forts and find the least defended fort at the
    chosen attack time.] The answer: within absolute or
    relative error less than 10^-6 of what a weakest fort
    faces at time [attack_time]. *)
Definition timing_spec
  (attack_time : N)
  (initial_strengths : list R )
  (link_sources link_targets : list N )
  (link_fractions : list R )
  (output : R)
  : Prop :=
  exists fort, fort < len initial_strengths /\
    (forall other, other < len initial_strengths ->
       (faced initial_strengths link_sources link_targets
         link_fractions
          (N.to_nat attack_time) fort
        <= faced initial_strengths link_sources link_targets
          link_fractions
             (N.to_nat attack_time) other)%R) /\
    let weakest := faced initial_strengths link_sources
      link_targets
                     link_fractions (N.to_nat attack_time)
            fort in
    (Rabs (output - weakest) < / 1000000 \/
     Rabs (output - weakest) < / 1000000 * Rabs weakest)%R.

(** ** Interface *)

(** Model transfers of strength between forts and find
    the least defended fort at the chosen attack time.
    - Input [attack_time]:
    - Input [initial_strengths]:
    - Input [link_sources]:
    - Input [link_targets]:
    - Input [link_fractions]:
    - Output [output]: *)
Program timing :
  uint -> array float -> array uint -> array uint ->
    array float -> float.

(** ** Bridge *)

(** [@requirement timing_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [timing_spec]. *)
Specification timing_correct :
  forall (attack_time : N) (initial_strengths : list R)
         (link_sources link_targets : list N )
           (link_fractions : list R )
         (attack_time_int : uint) (initial_strengths_arr :
           array float )
         (link_sources_arr link_targets_arr : array uint)
         (link_fractions_arr : array float),
    valid_input attack_time initial_strengths link_sources
      link_targets
      link_fractions ->
    repr attack_time_int attack_time ->
    repr initial_strengths_arr initial_strengths ->
    repr link_sources_arr link_sources ->
    repr link_targets_arr link_targets ->
    repr link_fractions_arr link_fractions ->
    exists output : R,
      repr (timing attack_time_int initial_strengths_arr
        link_sources_arr
              link_targets_arr link_fractions_arr) output /\
      timing_spec attack_time initial_strengths link_sources
        link_targets
        link_fractions output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
