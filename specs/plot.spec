(* @function        plot
   @signature       uint -> array sint -> array sint
   @math_signature  N -> list Z -> list Z
   @summary         [plot n a] takes the degree n and the n+1 coefficients
                    a_n, ..., a_1, a_0 of p in input order (a_n first) and
                    returns the n+1 constants C_0, ..., C_n with which the
                    statement's pseudocode produces p(i) at every integer
                    point i = 0, 1, 2, ...
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  The coefficients are listed as the input line gives them,
   a_n first; the constants C_0 first. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The value at x of the polynomial whose coefficients, highest degree
   first, are a: a_n x^n + ... + a_1 x + a_0. *)
Fixpoint pval (a : list Z) (x : Z) : Z :=
  match a with
  | [] => 0
  | c :: r => c * x ^ Z.of_nat (List.length r) + pval r x
  end.

(* One iteration of the pseudocode's loop body on the variables
   [p; t_1; ...; t_n]: each variable but the last is increased by the next
   one, read before that one is updated; t_n is unchanged. *)
Fixpoint step (v : list Z) : list Z :=
  match v with
  | x :: ((y :: _) as r) => (x + y) :: step r
  | _ => v
  end.

(* The value of p(i) that the pseudocode computes from the constants c:
   p(0) = C_0, t_k = C_k, then i iterations of the loop body. *)
Definition plotted (c : list Z) (i : N) : Z := hd 0 (N.iter i step c).

Record valid_input (n : N) (a : list Z) : Prop := {
  (* The first integer is n, where 1 <= n <= 6. *)
  vi_n : (1 <= n <= 6)%N;
  (* This is followed by n+1 integer coefficients a_n, ..., a_1, a_0. *)
  vi_len : len a = (n + 1)%N;
  (* You may assume that |a_i| <= 50 for all i, *)
  vi_coeffs : Forall (fun c => Z.abs c <= 50) a;
  (* and a_n <> 0. *)
  vi_lead : hd 0 a <> 0;
}.

(* The constants C_0, ..., C_n: n+1 of them, and with them the pseudocode
   gives the correct value p(i) at every i, so for every m at
   i = 0, ..., m-1. *)
Definition plot_spec (n : N) (a : list Z) (c : list Z) : Prop :=
  len c = (n + 1)%N /\
  forall i : N, plotted c i = pval a (Z.of_N i).

Program plot : uint -> array sint -> array sint.

Specification plot_correct :
  forall (n : N) (a : list Z) (x : uint) (y : array sint),
  valid_input n a -> repr x n -> repr y a ->
  exists c : list Z, repr (plot x y) c /\ plot_spec n a c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
