(* @function        basincity
   @signature       uint -> array (array uint) -> bool
   @math_signature  N -> list (list N) -> bool
   @summary         [basincity drone_count neighbour_lists] decides whether
                    exactly drone_count drones can be placed on drone_count
                    distinct intersections of Basin City so that no two
                    drones sit on neighbouring intersections (true for
                    "possible", false for "impossible").  Row
                    intersection-1 of neighbour_lists is the line of
                    intersection intersection (numbered 1..n): the numbers
                    of its at most four neighbours.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  neighbour_lists is the list of the n input lines,
   intersection intersection being described by line intersection (1-based,
   as in the statement). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* intersection is the number of an intersection. *)
Definition is_intersection (neighbour_lists : list (list N))
    (intersection : N) : Prop :=
  1 <= intersection <= len neighbour_lists.

(* The neighbour numbers given on the line of intersection intersection. *)
Definition line (neighbour_lists : list (list N)) (intersection : N)
    : list N :=
  nth (N.to_nat (intersection - 1)) neighbour_lists [].

(* other is listed as a neighbour of intersection. *)
Definition neighbours (neighbour_lists : list (list N))
    (intersection other : N) : Prop :=
  In other (line neighbour_lists intersection).

(* drone_spots is a placement of drone_count drones: drone_count distinct
   intersections, no two of them neighbours. *)
Definition placement (neighbour_lists : list (list N)) (drone_count : N)
    (drone_spots : list N) : Prop :=
  len drone_spots = drone_count /\
  NoDup drone_spots /\
  (forall intersection, In intersection drone_spots ->
     is_intersection neighbour_lists intersection) /\
  (forall intersection other,
     In intersection drone_spots -> In other drone_spots ->
     ~ neighbours neighbour_lists intersection other).

(* The statement's guarantees on the input. *)
Record valid_input (drone_count : N) (neighbour_lists : list (list N))
    : Prop := {
  (* 0 <= k <= 15, k the number of drones *)
  vi_k : drone_count <= 15;
  (* 1 <= n <= 100 000, the total number of intersections *)
  vi_n : 1 <= len neighbour_lists <= 100000;
  (* 0 <= d <= 4, the number of intersections neighbouring the i-th one *)
  vi_d : Forall (fun row => len row <= 4) neighbour_lists;
  (* the intersections are numbered from 1 to n *)
  vi_range : forall intersection other,
    is_intersection neighbour_lists intersection ->
    neighbours neighbour_lists intersection other ->
    is_intersection neighbour_lists other;
  (* the neighbours of the i-th intersection are all distinct ... *)
  vi_distinct : Forall (fun row => NoDup row) neighbour_lists;
  (* ... and different from i *)
  vi_irrefl : forall intersection,
    is_intersection neighbour_lists intersection ->
    ~ neighbours neighbour_lists intersection intersection;
  (* the d integers are the intersections neighbouring the i-th one, and
     neighbouring is mutual ("no two neighbouring intersections") *)
  vi_mutual : forall intersection other,
    is_intersection neighbour_lists intersection ->
    neighbours neighbour_lists intersection other ->
    neighbours neighbour_lists other intersection;
}.

(* "possible" exactly when some placement of drone_count drones exists. *)
Definition basincity_spec (drone_count : N) (neighbour_lists : list (list N))
    (output : bool) : Prop :=
  match output with
  | true =>
      exists drone_spots, placement neighbour_lists drone_count drone_spots
  | false =>
      ~ exists drone_spots, placement neighbour_lists drone_count drone_spots
  end.

(* machine side : the only thing that gets extracted *)
Program basincity : uint -> array (array uint) -> bool.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification basincity_correct :
  forall (drone_count : N) (neighbour_lists : list (list N))
         (drone_count_int : uint) (neighbour_lists_arr : array (array uint)),
  valid_input drone_count neighbour_lists ->
  repr drone_count_int drone_count ->
  repr neighbour_lists_arr neighbour_lists ->
  exists output : bool,
    repr (basincity drone_count_int neighbour_lists_arr) output /\
    basincity_spec drone_count neighbour_lists output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
