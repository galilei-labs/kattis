(** * Timing *)

(** ** Description *)

(** Enemy troops are stationed at forts connected by directed links. During
    each time step, every link transfers its specified fraction of the
    source fort's troop strength to the target. All transfers use the
    strengths at the beginning of the step and occur simultaneously;
    strength not sent away remains at its fort.

    After the given number of steps, choose a fort to attack. Its defenders
    include its own troops and reinforcements from every other fort directly
    linked to it in either direction. Each neighboring fort contributes once.
    Return the smallest combined defending strength over all possible targets.
    Strengths are real-valued indicators, not integer troop counts.

    [@kattis timing]
    - Difficulty: 3.5
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 100$; at most $(n-1)^2$ links; time steps: $0 \le t \le 5 \times 10^{3}$.
    - Initial quantities: $0 \le u_i \le 10^{3}$; each transfer fraction satisfies $0 < p_i \le 1$.
    - Outgoing transfers from a vertex total at most its available quantity. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives graph size and step count, initial quantities and fractional transfer edges.
    - Output convention: The minimum final neighborhood sum, with absolute or relative error below $10^{-6}$. *)
(* Input:
3
4 3 1
100 200 10 305
0 1 0.25
1 2 0.1
2 0 0.75
4 3 1
100 200 10 312
0 1 0.25
1 2 0.1
2 0 0.75
4 4 5
100 200 300 400
0 1 0.2
1 2 0.2
2 3 0.3
3 0 0.2
Output:
305.000000000
310.000000000
659.879000000
*)

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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope bool_scope.
Open Scope N_scope.

(* The links are three parallel lists, one per
   column of the input lines "s t p" ; a strength or a
   fraction is the real its float denotes. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_R (l : list R ) (k : N) : R := nth (N.to_nat
  k) l 0%R.
(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_N (l : list N ) (k : N) : N := nth (N.to_nat
  k) l 0.

(** The sum of [term] over zero-based indices below [count]. *)
Fixpoint sum_below (term : N -> R) (count : nat) : R :=
  match count with
  | O => 0%R
  | S count' =>
    (sum_below term count' + term (N.of_nat count'))%R
  end.

(** One simultaneous transfer step: add incoming transfers and subtract
    outgoing transfers, all computed from the current strengths. *)
Definition step
  (link_sources link_targets : list N) (link_fractions : list R)
  (current : N -> R) (fort : N) : R :=
  (current fort
   + sum_below (fun j => if get_N link_targets j =? fort
                        then get_R link_fractions j * current (get_N link_sources j)
                        else 0)
               (List.length link_sources)
   - sum_below (fun j => if get_N link_sources j =? fort
                        then get_R link_fractions j * current fort
                        else 0)
               (List.length link_sources))%R.

(** The strength of each fort after the given number of time steps. *)
Fixpoint strength
  (initial_strengths : list R)
  (link_sources link_targets : list N) (link_fractions : list R)
  (time : nat) : N -> R :=
  match time with
  | O => get_R initial_strengths
  | S time => step link_sources link_targets link_fractions
                  (strength initial_strengths link_sources link_targets link_fractions time)
  end.

(** Whether two distinct forts are joined by a link in either direction. *)
Definition joined
  (link_sources link_targets : list N) (fort other : N) : bool :=
  negb (fort =? other) &&
  existsb (fun j => (get_N link_sources j =? fort)
                    && (get_N link_targets j =? other)
                 || (get_N link_sources j =? other)
                    && (get_N link_targets j =? fort))
          (map N.of_nat (seq 0 (List.length link_sources))).

(** The defending strength at a fort: its own strength plus that of each
    directly linked neighbor, counted once. *)
Definition faced
  (initial_strengths : list R)
  (link_sources link_targets : list N) (link_fractions : list R)
  (time : nat) (fort : N) : R :=
  (strength initial_strengths link_sources link_targets link_fractions time fort
   + sum_below (fun other => if joined link_sources link_targets fort other
                            then strength initial_strengths link_sources link_targets
                                          link_fractions time other
                            else 0)
               (List.length initial_strengths))%R.

(** The total fraction a fort sends to other forts in one time step. *)
Definition outflow
  (link_sources link_targets : list N) (link_fractions : list R)
  (fort : N) : R :=
  sum_below (fun j => if (get_N link_sources j =? fort)
                        && negb (get_N link_targets j =? fort)
                     then get_R link_fractions j else 0%R)
            (List.length link_sources).

(** [@inside timing_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
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
  (* the time from now when to attack t (0 <= t <= 5 * 10^3) *)
  vi_t : attack_time <= 5000;
  (* l lines, each two integers s_j t_j and one double
     p_j *)
  vi_dst_len : len link_targets = len link_sources;
  vi_frac_len : len link_fractions = len link_sources;
  (* N doubles u_i (0 <= u_i <= 10^3) *)
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

(** [@requirement]
    The output approximates the smallest defending strength faced at any fort
    after the specified troop-transfer steps, counting the target and each
    directly linked neighboring fort once, regardless of link direction,
    within the specified absolute or relative tolerance. *)
Definition timing_spec
  (attack_time : N)
  (initial_strengths : list R )
  (link_sources link_targets : list N )
  (link_fractions : list R )
  (output : R)
  : Prop :=
  exists fort,
    let weakest := faced initial_strengths link_sources link_targets
                         link_fractions (N.to_nat attack_time) fort in
    fort < len initial_strengths /\
    (forall other, other < len initial_strengths ->
        (weakest <= faced initial_strengths link_sources link_targets
                          link_fractions (N.to_nat attack_time) other)%R) /\
    (Rabs (output - weakest) < / 1000000 \/
     Rabs (output - weakest) < / 1000000 * Rabs weakest)%R.

(** ** Interface *)

(** Find the weakest fort to attack after the scheduled troop transfers,
    counting defenders at the target and all its directly linked neighbors,
    regardless of link direction.
    - Input [attack_time]: Number of simultaneous troop-transfer steps before the attack.
    - Input [initial_strengths]: Initial troop-strength indicator at each fort.
    - Input [link_sources]: Fort sending troops along each directed link.
    - Input [link_targets]: Fort receiving troops along each corresponding link.
    - Input [link_fractions]: Fraction of the source strength transferred per step along each link.
    - Output [output]: Approximation of the minimum combined defending strength, within the specified absolute or relative tolerance. *)
Program timing :
  uint -> array float -> array uint -> array uint ->
    array float -> float.

(** [@example timing]
    - Sample: 1
    - Case: 1
    - Input [attack_time]: 1
    - Input [initial_strengths]: [100; 200; 10; 305]%R
    - Input [link_sources]: [0; 1; 2]
    - Input [link_targets]: [1; 2; 0]
    - Input [link_fractions]: [fval 0.25%float; fval 0.1%float; fval 0.75%float]
    - Output [output]: 305%R
*)

(** [@example timing]
    - Sample: 1
    - Case: 2
    - Input [attack_time]: 1
    - Input [initial_strengths]: [100; 200; 10; 312]%R
    - Input [link_sources]: [0; 1; 2]
    - Input [link_targets]: [1; 2; 0]
    - Input [link_fractions]: [fval 0.25%float; fval 0.1%float; fval 0.75%float]
    - Output [output]: 310%R
*)

(** [@example timing]
    - Sample: 1
    - Case: 3
    - Input [attack_time]: 5
    - Input [initial_strengths]: [100; 200; 300; 400]%R
    - Input [link_sources]: [0; 1; 2; 3]
    - Input [link_targets]: [1; 2; 3; 0]
    - Input [link_fractions]: [fval 0.2%float; fval 0.2%float; fval 0.3%float; fval 0.2%float]
    - Output [output]: fval 659.879%float
*)

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
