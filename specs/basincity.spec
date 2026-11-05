(* @function        basincity
   @signature       uint -> array (array uint) -> bool
   @math_signature  N -> list (list N) -> bool
   @summary         [basincity k adj] decides whether exactly k drones can
                    be placed on k distinct intersections of Basin City so
                    that no two drones sit on neighbouring intersections
                    (true for "possible", false for "impossible").  Row x-1
                    of adj is the line of intersection x (numbered 1..n):
                    the numbers of its at most four neighbours.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  adj is the list of the n input lines, intersection x being
   described by line x (1-based, as in the statement). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* x is the number of an intersection. *)
Definition is_intersection (adj : list (list N)) (x : N) : Prop :=
  1 <= x <= len adj.

(* The neighbour numbers given on the line of intersection x. *)
Definition line (adj : list (list N)) (x : N) : list N :=
  nth (N.to_nat (x - 1)) adj [].

(* y is listed as a neighbour of x. *)
Definition neighbours (adj : list (list N)) (x y : N) : Prop :=
  In y (line adj x).

(* ds is a placement of k drones: k distinct intersections, no two of them
   neighbours. *)
Definition placement (adj : list (list N)) (k : N) (ds : list N) : Prop :=
  len ds = k /\
  NoDup ds /\
  (forall x, In x ds -> is_intersection adj x) /\
  (forall x y, In x ds -> In y ds -> ~ neighbours adj x y).

(* The statement's guarantees on the input. *)
Record valid_input (k : N) (adj : list (list N)) : Prop := {
  (* 0 <= k <= 15 *)
  vi_k : k <= 15;
  (* 1 <= n <= 100 000, the total number of intersections *)
  vi_n : 1 <= len adj <= 100000;
  (* 0 <= d <= 4, the number of intersections neighbouring the i-th one *)
  vi_d : Forall (fun l => len l <= 4) adj;
  (* the intersections are numbered from 1 to n *)
  vi_range : forall x y, is_intersection adj x -> neighbours adj x y ->
               is_intersection adj y;
  (* the neighbours of the i-th intersection are all distinct ... *)
  vi_distinct : Forall (fun l => NoDup l) adj;
  (* ... and different from i *)
  vi_irrefl : forall x, is_intersection adj x -> ~ neighbours adj x x;
  (* the d integers are the intersections neighbouring the i-th one, and
     neighbouring is mutual ("no two neighbouring intersections") *)
  vi_mutual : forall x y, is_intersection adj x -> neighbours adj x y ->
                neighbours adj y x;
}.

(* "possible" exactly when some placement of k drones exists. *)
Definition basincity_spec (k : N) (adj : list (list N)) (b : bool) : Prop :=
  b = true <-> exists ds, placement adj k ds.

(* machine side : the only thing that gets extracted *)
Program basincity : uint -> array (array uint) -> bool.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification basincity_correct :
  forall (k : N) (adj : list (list N)) (x : uint) (y : array (array uint)),
  valid_input k adj -> repr x k -> repr y adj ->
  exists b : bool, repr (basincity x y) b /\ basincity_spec k adj b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
