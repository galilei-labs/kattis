(* @function        signed_area2
   @signature       array sint -> array sint -> sint
   @math_signature  list Z -> list Z -> Z
   @summary         [signed_area2 xs ys] returns twice the signed area of
                    the polygon whose vertices are (xs[i], ys[i]) in order :
                    positive when they are given counterclockwise, negative
                    when clockwise.  The harness prints the direction from
                    the sign and the area, half the absolute value, with
                    one decimal
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_Z (l : list Z) (k : N) : Z := nth (N.to_nat k) l 0.

(* The vertex after i, the last one being followed by the first. *)
Definition next (n i : N) : N := ((i + 1) mod n)%N.

(* f 0 + f 1 + ... + f (n - 1). *)
Fixpoint sum_below (f : N -> Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S m => sum_below f m + f (N.of_nat m)
  end.

(* The shoelace sum, twice the signed area : the sum over the vertices of
   x_i * y_(i+1) - x_(i+1) * y_i. *)
Definition shoelace (xs ys : list Z) : Z :=
  let n := len xs in
  sum_below (fun i => get_list_Z xs i * get_list_Z ys (next n i)
                      - get_list_Z xs (next n i) * get_list_Z ys i)
            (N.to_nat n).

(* The statement's bounds, for one test case.  The statement also says the
   vertices are those of a simple polygon ; the shoelace sum does not
   need it, so it is not stated. *)
Record valid_input (xs ys : list Z) : Prop := {
  (* 3 <= n <= 1000 *)
  vi_n : (3 <= len xs <= 1000)%N;
  (* one y per x *)
  vi_ys_length : len ys = len xs;
  (* coordinates are integers with absolute value bounded by 10000 *)
  vi_xs : Forall (fun x => - 10000 <= x <= 10000) xs;
  vi_ys : Forall (fun y => - 10000 <= y <= 10000) ys;
}.

(* The answer : the shoelace sum. *)
Definition signed_area2_spec (xs ys : list Z) (v : Z) : Prop :=
  v = shoelace xs ys.

(* machine side : the only thing that gets extracted *)
Program signed_area2 : array sint -> array sint -> sint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification signed_area2_correct : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists v : Z, repr (signed_area2 x y) v /\ signed_area2_spec xs ys v.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
