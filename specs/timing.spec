(* @function        timing
   @signature       uint -> array float -> array uint -> array uint -> array float -> float
   @math_signature  N -> list R -> list N -> list N -> list R -> R
   @summary         One test case: [timing t u src dst frac] takes N forts
                    holding the strengths u and l links, link j moving in
                    every time unit the fraction frac_j of the units of fort
                    src_j (as they were at the start of the unit) to fort
                    dst_j. After t time units an attack on a fort faces its
                    own strength plus that of every other fort joined to it
                    by a link, in either direction; the result is the lowest
                    such value over the forts, with an absolute or relative
                    error less than 10^-6.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope bool_scope.
Open Scope N_scope.

(* Math side.  The links are three parallel lists, one per column of the
   input lines "s t p"; a strength or a fraction is the real its float
   denotes. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element, for k < len l (0 outside, never relied on). *)
Definition get_R (l : list R) (k : N) : R := nth (N.to_nat k) l 0%R.
Definition get_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* f 0 + f 1 + ... + f (n - 1). *)
Fixpoint sum_below (f : N -> R) (n : nat) : R :=
  match n with
  | O => 0%R
  | S m => (sum_below f m + f (N.of_nat m))%R
  end.

Section Galaxy.

  Variables (u : list R) (src dst : list N) (frac : list R).

  (* One time unit, from the strengths v: fort i receives frac_j * v(src_j)
     over every link j into it and loses frac_j * v(i) over every link j
     out of it (a link from i to i gives and takes the same amount). *)
  Definition step (v : N -> R) (i : N) : R :=
    (v i
     + sum_below (fun j => if get_N dst j =? i
                           then get_R frac j * v (get_N src j) else 0)
                 (List.length src)
     - sum_below (fun j => if get_N src j =? i
                           then get_R frac j * v i else 0)
                 (List.length src))%R.

  (* The strength of each fort after k time units. *)
  Fixpoint strength (k : nat) : N -> R :=
    match k with
    | O => get_R u
    | S k => step (strength k)
    end.

  (* Forts i and m are distinct and some link joins them, in either
     direction. *)
  Definition joined (i m : N) : bool :=
    negb (i =? m) &&
    existsb (fun j => (get_N src j =? i) && (get_N dst j =? m)
                   || (get_N src j =? m) && (get_N dst j =? i))
            (map N.of_nat (seq 0 (List.length src))).

  (* What an attack on fort i faces after k time units: its own strength
     and that of every fort joined to it. *)
  Definition faced (k : nat) (i : N) : R :=
    (strength k i
     + sum_below (fun m => if joined i m then strength k m else 0)
                 (List.length u))%R.

  (* The total fraction fort i sends to other forts in one time unit. *)
  Definition outflow (i : N) : R :=
    sum_below (fun j => if (get_N src j =? i) && negb (get_N dst j =? i)
                        then get_R frac j else 0%R)
              (List.length src).

End Galaxy.

(* The statement's bounds, for one test case (1 <= T <= 10 test cases:
   one call per test case). *)
Record valid_input (t : N) (u : list R) (src dst : list N) (frac : list R)
  : Prop := {
  (* the number of enemy forts N (1 <= N <= 100) *)
  vi_N : 1 <= len u <= 100;
  (* the number of links l (0 <= l <= (N-1)^2) *)
  vi_l : len src <= (len u - 1) ^ 2;
  (* the time from now when to attack t (0 <= t <= 5000) *)
  vi_t : t <= 5000;
  (* l lines, each two integers s_j t_j and one double p_j *)
  vi_dst_len : len dst = len src;
  vi_frac_len : len frac = len src;
  (* N doubles u_i (0 <= u_i <= 1000) *)
  vi_u : Forall (fun x => 0 <= x <= 1000)%R u;
  (* s_j (0 <= s_j < N), t_j (0 <= t_j < N) *)
  vi_src : Forall (fun s => s < len u) src;
  vi_dst : Forall (fun d => d < len u) dst;
  (* one double p_j (0 < p_j <= 1) *)
  vi_frac : Forall (fun p => 0 < p <= 1)%R frac;
  (* "for each fort a fraction of the units is moved to other forts in
     each time unit": what leaves a fort is a fraction of its units, at
     most 1.  The slack 10^-9 is there because the decimals p_j are
     received as doubles, whose reals may sum to slightly more than 1
     when the decimals sum to exactly 1 (fval 0.2 + fval 0.8 = 1 + 5.6e-17;
     each double is within a relative 2^-53 of its decimal) *)
  vi_outflow : forall i, i < len u ->
    (outflow src dst frac i <= 1 + / 1000000000)%R;
}.

(* The answer: within absolute or relative error less than 10^-6 of what
   a weakest fort faces at time t. *)
Definition timing_spec (t : N) (u : list R) (src dst : list N)
  (frac : list R) (o : R) : Prop :=
  exists i, i < len u /\
    (forall m, m < len u ->
       (faced u src dst frac (N.to_nat t) i
        <= faced u src dst frac (N.to_nat t) m)%R) /\
    let a := faced u src dst frac (N.to_nat t) i in
    (Rabs (o - a) < / 1000000 \/ Rabs (o - a) < / 1000000 * Rabs a)%R.

Program timing :
  uint -> array float -> array uint -> array uint -> array float -> float.

Specification timing_correct :
  forall (t : N) (u : list R) (src dst : list N) (frac : list R)
         (xt : uint) (xu : array float) (xs xd : array uint)
         (xf : array float),
    valid_input t u src dst frac ->
    repr xt t -> repr xu u -> repr xs src -> repr xd dst -> repr xf frac ->
    exists o : R, repr (timing xt xu xs xd xf) o /\
                  timing_spec t u src dst frac o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
