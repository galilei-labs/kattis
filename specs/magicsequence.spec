(* @function        magic
   @signature       uint -> uint -> uint -> uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N -> N -> N -> N
   @summary         [magic n a b c x y] generates the sequence S of n
                    integers S[0] = a, S[i] = (S[i-1] * b + a) mod c for
                    1 <= i < n, sorts it into R, and returns the hash V
                    obtained from V = 0 by V := (V * x + R[i]) mod y for i
                    from 0 to n - 1.  One test case per call.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* S[i] : S[0] = a, S[i] = (S[i-1] * b + a) mod c. *)
Fixpoint term (a b c : N) (i : nat) : N :=
  match i with
  | O => a
  | Datatypes.S k => (term a b c k * b + a) mod c
  end.

(* The sequence S[0], ..., S[n-1]. *)
Definition sequence (n a b c : N) : list N :=
  map (term a b c) (seq 0 (N.to_nat n)).

(* r is the sorted version of s : the same elements, in non-decreasing order. *)
Definition sorted_version (r s : list N) : Prop :=
  Permutation r s /\ Sorted N.le r.

(* The value of V after "V = 0; for each e of r in order : V = (V * x + e) % y". *)
Definition hash (x y : N) (r : list N) : N :=
  fold_left (fun v e => (v * x + e) mod y) r 0.

(* The statement's bounds, for one test case (TC, the number of test cases,
   is the harness's loop, not an argument). *)
Record valid_input (n a b c x y : N) : Prop := {
  (* 1 <= N <= 10^6 *)
  vi_n : 1 <= n <= 10 ^ 6;
  (* 1 <= A, B, C <= 10^9 *)
  vi_a : 1 <= a <= 10 ^ 9;
  vi_b : 1 <= b <= 10 ^ 9;
  vi_c : 1 <= c <= 10 ^ 9;
  (* 1 <= X, Y <= 10^9 *)
  vi_x : 1 <= x <= 10 ^ 9;
  vi_y : 1 <= y <= 10 ^ 9;
}.

(* The answer is the hash of R, the sorted version of S (R is unique, so
   the answer is pinned). *)
Definition magic_spec (n a b c x y v : N) : Prop :=
  exists r, sorted_version r (sequence n a b c) /\ v = hash x y r.

Program magic : uint -> uint -> uint -> uint -> uint -> uint -> uint.

Specification magic_correct :
  forall (n a b c x y : N) (n' a' b' c' x' y' : uint),
  valid_input n a b c x y ->
  repr n' n -> repr a' a -> repr b' b -> repr c' c -> repr x' x -> repr y' y ->
  exists v : N, repr (magic n' a' b' c' x' y') v /\ magic_spec n a b c x y v.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
