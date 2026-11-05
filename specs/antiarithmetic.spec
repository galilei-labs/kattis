(* @function        antiarithmetic
   @signature       array uint -> bool
   @math_signature  list N -> bool
   @summary         [antiarithmetic p] decides whether the permutation p of
                    0, 1, ..., n-1 (n the length of p) is antiarithmetic: it
                    returns true exactly when there are no three indices
                    0 <= i < j < k < n such that (p_i, p_j, p_k) forms an
                    arithmetic progression.  One call per test case.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A permutation is the list of its values, p_0 first. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The i-th element of p (p_i); 0 beyond the end. *)
Definition get (p : list N) (i : N) : N := nth (N.to_nat i) p 0.

(* (a, b, c) forms an arithmetic progression: there is a constant c0 with
   a - b = c0 and b - c = c0, the differences taken in Z. *)
Definition progression (a b c : N) : Prop :=
  (Z.of_N a - Z.of_N b = Z.of_N b - Z.of_N c)%Z.

(* There are three indices 0 <= i < j < k < n such that (p_i, p_j, p_k)
   forms an arithmetic progression. *)
Definition has_progression (p : list N) : Prop :=
  exists i j k : N,
    i < j /\ j < k /\ k < len p /\
    progression (get p i) (get p j) (get p k).

(* p is antiarithmetic: no subsequence of it of length greater than 2 is
   an arithmetic progression. *)
Definition is_antiarithmetic (p : list N) : Prop := ~ has_progression p.

(* The statement's guarantees, for one test case (n = len p). *)
Record valid_input (p : list N) : Prop := {
  (* a natural number 3 <= n <= 10 000 *)
  vi_n : 3 <= len p <= 10000;
  (* all n numbers are nonnegative integers smaller than n *)
  vi_values : Forall (fun v => v < len p) p;
  (* followed by n distinct numbers *)
  vi_distinct : NoDup p;
}.

(* The answer: yes (true) exactly when p is antiarithmetic, no (false)
   exactly when some three of its terms, in order, form a progression. *)
Definition antiarithmetic_spec (p : list N) (b : bool) : Prop :=
  (b = true <-> is_antiarithmetic p) /\
  (b = false <-> has_progression p).

(* machine side : the only thing that gets extracted *)
Program antiarithmetic : array uint -> bool.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification antiarithmetic_correct : forall (p : list N) (x : array uint),
  valid_input p -> repr x p ->
  exists b : bool, repr (antiarithmetic x) b /\ antiarithmetic_spec p b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
