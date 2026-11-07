(** * Plotting Polynomials *)

(** ** Description *)

(** [plot degree coefficients] takes the degree n and the n+1
    coefficients a_n, ..., a_1, a_0 of p in input order (a_n first)
    and returns the n+1 constants C_0, ..., C_n with which the
    statement's pseudocode produces p(i) at every integer point i =
    0, 1, 2, . *)

(** [@kattis plot]
    - Difficulty: 2.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB *)

(** ** Examples *)

(** Kattis sample: text input and output. *)
(* 1 5 2 = 2 5 *)

(** Kattis sample: text input and output. *)
(* 2 2 -4 5 = 5 -2 4 *)

(** ** [@hide] Environment *)
(* @function        plot
   @signature       uint -> array sint -> array sint
   @math_signature  N -> list Z -> list Z
   @summary         [plot degree coefficients] takes the degree n and the
                    n+1 coefficients a_n, ..., a_1, a_0 of p in input order
                    (a_n first) and returns the n+1 constants C_0, ..., C_n
                    with which the statement's pseudocode produces p(i) at
                    every integer point i = 0, 1, 2, ...
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** Math side. The coefficients are listed as the input line gives them,
    a_n first; the constants C_0 first. The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The value at point of the polynomial whose coefficients, highest
    degree first, are coefficients: a_n point^n + ... + a_1 point +
    a_0. *)
Fixpoint pval (coefficients : list Z) (point : Z) : Z :=
  match coefficients with
  | [] => 0
  | leading :: lower =>
      leading * point ^ Z.of_nat (List.length lower) + pval
        lower point
  end.

(** One iteration of the pseudocode's loop body on the variables [p;
    t_1; ...; t_n]: each variable but the last is increased by the
    next one, read before that one is updated; t_n is unchanged. *)
Fixpoint step (variables : list Z) : list Z :=
  match variables with
  | current :: ((following :: _) as rest) => (current +
    following) :: step rest
  | _ => variables
  end.

(** The value of p(point) that the pseudocode computes from the
    constants: p(0) = C_0, t_k = C_k, then point iterations of the
    loop body. *)
Definition plotted (constants : list Z) (point : N) : Z :=
  hd 0 (N.iter point step constants).

(** [@inside plot_correct] The [valid_input] datatype. *)
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

(** [@requirement] [@short The constants C_0, ..., C_n: n+1 of them, and
    with them the pseudocode    gives the correct value p(point) at
    every point, so for every m at    point = 0, ..., m-1.] The
    constants C_0, ..., C_n: n+1 of them, and with them the
    pseudocode gives the correct value p(point) at every point, so
    for every m at point = 0, ..., m-1. *)
Definition plot_spec (degree : N) (coefficients : list Z)
    (output : list Z) : Prop :=
  len output = (degree + 1)%N /\
  forall point : N, plotted output point = pval coefficients
    (Z.of_N point).

(** ** Interface *)

(** The [plot] program on machine values.
    - Input [degree]:
    - Input [coefficients]:
    - Output [output]: *)
Program plot : uint -> array sint -> array sint.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
