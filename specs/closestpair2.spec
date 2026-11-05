(* @function        closestpair
   @signature       array sint -> array sint -> uint * uint
   @math_signature  list Q -> list Q -> N * N
   @summary         One test case: [closestpair xs ys] takes the n >= 2
                    points (xs_k, ys_k) of the case, coordinates being exact
                    decimals with at most two fractional digits, and returns
                    the indices i, j of two distinct points whose squared
                    Euclidean distance is minimal among all pairs of distinct
                    points, exactly; any such pair, in either order. The
                    harness prints xs_i ys_i xs_j ys_j.
*)

From Stdlib Require Import ZArith NArith QArith Qabs List Uint63 Sint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Q_scope.

(* Machine coordinates.  The OCaml harness parses each coordinate text
   exactly ("1.12", "-884.2", "158" become 112, -88420, 15800): a machine
   coordinate is a [sint] word counting hundredths, and it represents the
   rational number of that many hundredths.  [Q] rather than [Z]
   hundredths on the math side so that the contract speaks of the
   statement's coordinates themselves, in the statement's unit. *)
Instance repr_hundredths : Repr sint Q :=
  fun x c => c == (Sint63.to_Z x # 100).

(* Math side.  The points are two parallel lists, one per column of the
   input lines "x y". *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th coordinate, for k < len l (0 outside, never relied on). *)
Definition get_list_Q (l : list Q) (k : N) : Q := nth (N.to_nat k) l 0.

(* i and j are two distinct points of the input: distinct indices; two
   indices may hold the same point, at distance 0 (third sample case). *)
Definition point_pair (xs : list Q) (i j : N) : Prop :=
  (i < len xs)%N /\ (j < len xs)%N /\ i <> j.

(* The squared Euclidean distance between points i and j. *)
Definition dist2 (xs ys : list Q) (i j : N) : Q :=
  let dx := get_list_Q xs i - get_list_Q xs j in
  let dy := get_list_Q ys i - get_list_Q ys j in
  dx * dx + dy * dy.

(* c has at most two decimals: it is a whole number of hundredths. *)
Definition two_decimals (c : Q) : Prop := exists k : Z, c == k # 100.

(* The statement's bounds on one test case. *)
Record valid_input (xs ys : list Q) : Prop := {
  (* 2 <= n <= 100 000 *)
  vi_n : (2 <= len xs <= 100000)%N;
  (* n points, one per line, each of the form x y *)
  vi_ys : len ys = len xs;
  (* coordinates are floating point values with at most 2 decimals *)
  vi_x_dec : Forall two_decimals xs;
  vi_y_dec : Forall two_decimals ys;
  (* ... and absolute value bounded by 100 000 *)
  vi_x : Forall (fun c => Qabs c <= 100000) xs;
  vi_y : Forall (fun c => Qabs c <= 100000) ys;
}.

(* The answer, "any closest pair": two distinct points that no pair of
   distinct points is strictly closer than, exactly.  Both point_pair and
   dist2 are symmetric in i and j, so (i, j) and (j, i) are equally
   accepted. *)
Definition closestpair_spec (xs ys : list Q) (r : N * N) : Prop :=
  point_pair xs (fst r) (snd r) /\
  forall p q, point_pair xs p q -> dist2 xs ys (fst r) (snd r) <= dist2 xs ys p q.

Program closestpair : array sint -> array sint -> uint * uint.

Specification closestpair_correct :
  forall (xs ys : list Q) (x y : array sint),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists r : N * N, repr (closestpair x y) r /\ closestpair_spec xs ys r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
