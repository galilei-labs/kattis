(* @function        median
   @signature       array uint -> float
   @math_signature  list N -> R
   @summary         [median a] is the median of the n >= 1 integers of a:
                    once they are sorted, the middle one when n is odd, the
                    mean of the two middle ones when n is even.  The float
                    returned denotes exactly that number (an integer or an
                    integer plus one half); no tolerance.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Stdlib Require Import Sorted Permutation.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The input is the list of the n integers, in input order.
   The output is a float because the mean of two integers need not be an
   integer (it is the real it denotes, exactly). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The element at 0-based position k of l, as a real (0 outside, never
   relied on). *)
Definition elem (l : list N) (k : N) : R := IZR (Z.of_N (nth (N.to_nat k) l 0)).

(* The median of a sorted list of n numbers: its element at 0-based
   position n / 2 when n is odd, the mean of its elements at n / 2 - 1 and
   n / 2 when n is even. *)
Definition median_of_sorted (l : list N) : R :=
  let n := len l in
  if N.odd n then elem l (n / 2)
  else ((elem l (n / 2 - 1) + elem l (n / 2)) / 2)%R.

(* The statement's bounds. *)
Record valid_input (a : list N) : Prop := {
  (* a single integer, n, where 1 <= n <= 10^5 *)
  vi_n : 1 <= len a <= 10 ^ 5;
  (* each integer is between 0 and 10^9 (inclusive) *)
  vi_a : Forall (fun v => v <= 10 ^ 9) a;
}.

(* The answer: the median of the input once sorted (the sorted
   rearrangement of the input exists and is unique). *)
Definition median_spec (a : list N) (r : R) : Prop :=
  forall l, Permutation a l -> Sorted N.le l -> r = median_of_sorted l.

Program median : array uint -> float.

Specification median_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists r : R, repr (median x) r /\ median_spec a r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
