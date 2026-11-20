(** * Plotting Polynomials *)

(** ** Description *)

(** Plot a polynomial at the integer inputs $0, 1, 2, \ldots$ using only
    additions after initialization. Find initial constants $C_0, \ldots, C_n$
    so that the first entry initially equals the polynomial's value at zero.
    To advance to the next input, replace every entry except the last by
    itself plus its next entry, using the old values for all additions.
    The last entry stays fixed. The first entry must then give the next
    polynomial value.

    These constants are the initial finite differences. For example, for
    $p(x) = x^2$, start with $(0, 1, 2)$; successive updates give
    $(1, 3, 2)$, $(4, 5, 2)$, and $(9, 7, 2)$, producing $0, 1, 4, 9$.

    [@kattis plot]
    - Difficulty: 2.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Polynomial degree: $1 \le n \le 6$.
    - Integer coefficients with absolute value at most $50$; leading
      coefficient nonzero. *)

(** ** Examples *)

(** - Input convention: Polynomial degree, followed by coefficients in descending degree order.
    - Output convention: Initial finite-difference constants C0 through Cn, separated by spaces. *)
(* Input:
1 5 2
Output:
2 5
*)

(** ** [@hide] Environment *)
(* @function        plot
   @signature       uint -> array sint -> array sint
   @math_signature  N -> list Z -> list Z
   @summary         [plot degree coefficients] takes the degree n and the
                    n+1 coefficients a_n, ..., a_1, a_0 of p in input order
                    (a_n first) and returns the n+1 constants C_0, ..., C_n
                    with which the statement's pseudocode produces p(i) at
                    every integer point i = 0, 1, 2, ...
                    It runs in at most c1 * (n + 1)^2 + c2 steps of the cost
                    model on a valid input, n the degree (the finite-
                    difference table), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Evaluate the polynomial [coefficients] at [point], with coefficients in
    decreasing degree order. *)
Fixpoint pval (coefficients : list Z) (point : Z) : Z :=
  match coefficients with
  | [] => 0
  | leading :: lower =>
      leading * point ^ Z.of_nat (List.length lower) + pval
        lower point
  end.

(** Perform one finite-difference update: add each entry's old successor to it,
    leaving the last entry unchanged. *)
Fixpoint step (variables : list Z) : list Z :=
  match variables with
  | current :: ((following :: _) as rest) => (current +
    following) :: step rest
  | _ => variables
  end.

(** The first entry after [point] finite-difference updates beginning with
    [constants]. *)
Definition plotted (constants : list Z) (point : N) : Z :=
  hd 0 (N.iter point step constants).

(** [@inside plot_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (degree : N)
  (coefficients : list Z) : Prop := {
  (* The first integer is n, where 1 <= n <= 6. *)
  vi_n : (1 <= degree <= 6)%N;
  (* This is followed by n+1 integer coefficients a_n,
     ..., a_1, a_0. *)
  vi_len : len coefficients = (degree + 1)%N;
  (* You may assume that |a_i| <= 50 for all i, *)
  vi_coeffs : Forall (fun coefficient => Z.abs coefficient
    <= 50)
                coefficients;
  (* and a_n <> 0. *)
  vi_lead : hd 0 coefficients <> 0;
}.

(** ** Correctness *)

(** [@requirement]
    The output contains the initial finite differences that generate the polynomial's
    values at every nonnegative integer input. *)
Definition plot_spec (degree : N) (coefficients : list Z)
    (output : list Z) : Prop :=
  len output = (degree + 1)%N /\
  forall point : N, plotted output point = pval coefficients
    (Z.of_N point).

(** ** Complexity *)

(** [@requirement] Runs in $O((d+1)^2)$ steps, where $d$ is the polynomial degree. *)
Definition plot_time_spec (c1 c2 n_degree steps : nat) : Prop :=
  (steps <= c1 * ((n_degree + 1) * (n_degree + 1)) + c2)%nat.

(** ** Interface *)

(** Initialize an addition-only polynomial plotter: the first returned entry
    is the value at zero. Each simultaneous update adds every entry's old
    successor to it, leaving the last unchanged; the first entry then gives
    the polynomial value at the next integer input.
    - Input [degree]: Degree of the polynomial.
    - Input [coefficients]: Coefficients $a_n,\ldots,a_0$ in decreasing degree order.
    - Output [output]: The output contains the initial finite differences that generate the polynomial's values at every nonnegative integer input. *)
Program plot : uint -> array sint -> array sint.

(** [@example plot]
    - Sample: 1
    - Input [degree]: 1
    - Input [coefficients]: [5; 2]%Z
    - Output [output]: [2; 5]%Z
*)

(** ** Bridge *)

(** [@requirement plot_spec] [@fold full correctness statement] On valid
    represented inputs, [plot] returns a represented output
    satisfying [plot_spec]. *)
Specification plot_correct :
  forall (degree : N) (coefficients : list Z) (degree_int :
    uint)
         (coefficients_arr : array sint),
  valid_input degree coefficients ->
    repr degree_int degree ->
  repr coefficients_arr coefficients ->
  exists output : list Z,
    repr (plot degree_int coefficients_arr) output /\
    plot_spec degree coefficients output.

(** ** Complexity *)

(** [@hide] [plot_cost] is the cost translation of [plot] (the judge
    recomputes it and compares) ... *)
Complexity plot_cost for plot.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1)^2 + c2 steps of the cost model on a valid input, n the degree (the finite-difference table), for two constants
    quantified before the inputs, on every valid input. [@requirement plot_time_spec] *)
Specification plot_time : exists c1 c2 : nat,
  forall (degree : N) (coefficients : list Z) (degree_int :
  uint)
  (coefficients_arr : array sint),
  valid_input degree coefficients ->
  repr degree_int degree ->
  repr coefficients_arr coefficients ->
  plot_time_spec c1 c2 (size degree_int) (cost2 plot_cost degree_int coefficients_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
