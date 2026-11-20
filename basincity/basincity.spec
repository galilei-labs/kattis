(** * Basin City Surveillance *)

(** ** Description *)

(** The police want to place traffic drones at city intersections. A drone
    must not be placed at an intersection directly connected by a street to
    another drone's intersection. Decide whether exactly the requested number
    of drones can be placed at distinct intersections under this restriction.
    Each intersection has at most four neighbors. Intersections and streets
    form an undirected graph; valid drone locations form an independent set.

    [@kattis basincity]
    - Difficulty: 8.2
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 10^{5}$; requested set size: $0 \le k \le 15$.
    - At most four distinct neighbors per vertex; no self-loops. *)

(** ** Examples *)

(** - Input convention: Requested independent-set size, vertex count, then degree-prefixed adjacency lists with 1-based indices.
    - Output convention: possible if a sufficiently large independent set exists; impossible otherwise. *)
(* Input:
4
7
2 2 4
3 1 3 5
1 2
2 1 5
4 2 6 4 7
2 5 7
2 6 5
Output:
impossible
*)

(** ** [@hide] Environment *)

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
                    It runs in at most c1 * (5^k * (n + 1) + m) + c2 steps
                    of the cost model on a valid input, k the number of
                    drones, n the number of lines and m the total length of
                    the neighbour lists ([sizes]): a search tree of depth at
                    most k with at most five children per node (the vertex
                    and its four neighbours), a linear scan per node; the
                    4^k of the binding branching rule is not stated, for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* neighbour_lists is the list of the n input
  lines,
   intersection intersection being described by line
     intersection (1-based,
   as in the statement). *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** [intersection] is a valid intersection number. *)
Definition is_intersection (neighbour_lists : list (list N))
    (intersection : N) : Prop :=
  1 <= intersection <= len neighbour_lists.

(** The list of neighbours supplied for [intersection]. *)
Definition line (neighbour_lists : list (list N))
  (intersection : N)
    : list N :=
  nth (N.to_nat (intersection - 1)) neighbour_lists [].

(** [other] is listed as a neighbour of [intersection]. *)
Definition neighbours (neighbour_lists : list (list N))
    (intersection other : N) : Prop :=
  In other (line neighbour_lists intersection).

(** [drone_spots] contains [drone_count] distinct intersections, with no two
    adjacent. *)
Definition placement (neighbour_lists : list (list N))
  (drone_count : N)
    (drone_spots : list N) : Prop :=
  len drone_spots = drone_count /\
  NoDup drone_spots /\
  (forall intersection, In intersection drone_spots ->
     is_intersection neighbour_lists intersection) /\
  (forall intersection other,
     In intersection drone_spots -> In other drone_spots ->
     ~ neighbours neighbour_lists intersection other).

(** [@inside basincity_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (drone_count : N)
  (neighbour_lists : list (list N))
    : Prop := {
  (* 0 <= k <= 15, k the number of drones *)
  vi_k : drone_count <= 15;
  (* 1 <= n <= 10^5, the total number of intersections *)
  vi_n : 1 <= len neighbour_lists <= 100000;
  (* 0 <= d <= 4, the number of intersections neighbouring
    the i-th one *)
  vi_d : Forall (fun row => len row <= 4) neighbour_lists;
  (* the intersections are numbered from 1 to n *)
  vi_range : forall intersection other,
    is_intersection neighbour_lists intersection ->
    neighbours neighbour_lists intersection other ->
    is_intersection neighbour_lists other;
  (* the neighbours of the i-th intersection are all
    distinct ... *)
  vi_distinct : Forall
    (fun row => NoDup row) neighbour_lists;
  (* ... and different from i *)
  vi_irrefl : forall intersection,
    is_intersection neighbour_lists intersection ->
    ~ neighbours neighbour_lists intersection intersection;
  (* the d integers are the intersections neighbouring the
    i-th one, and
     neighbouring is mutual
       ("no two neighbouring intersections") *)
  vi_mutual : forall intersection other,
    is_intersection neighbour_lists intersection ->
    neighbours neighbour_lists intersection other ->
    neighbours neighbour_lists other intersection;
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when the requested number of drones can be
    placed at distinct intersections with no two at neighboring intersections. *)
Definition basincity_spec (drone_count : N)
  (neighbour_lists : list (list N))
    (output : bool) : Prop :=
  output = true <->
    exists drone_spots, placement neighbour_lists
      drone_count drone_spots.

(** ** Complexity *)

(** [@requirement] Runs in $O(5^k(n+1)+L)$ steps, where $k$ is the drone count, $n$ the number of neighbour lists, and $L$ their total length. *)
Definition basincity_time_spec (c1 c2 n_drone_count n_neighbour_lists total_neighbour_lists steps : nat) : Prop :=
  (steps <= c1 * (5 ^ (n_drone_count) * (n_neighbour_lists + 1) + total_neighbour_lists + 1) + c2)%nat.

(** ** Interface *)

(** Decide whether the requested number of traffic drones can be placed at
    distinct intersections with no two at neighboring intersections.
    - Input [drone_count]: Number of drones to place.
    - Input [neighbour_lists]: Directly neighboring intersections for each intersection, using one-based intersection numbers.
    - Output [output]: [true] exactly when a placement of all requested drones exists. *)
Program basincity : uint -> array (array uint) -> bool.

(** [@example basincity]
    - Sample: 1
    - Input [drone_count]: 4
    - Input [neighbour_lists]: [[2; 4]; [1; 3; 5]; [2]; [1; 5]; [2; 6; 4; 7]; [5; 7]; [6; 5]]
    - Output [output]: false
*)

(** ** Bridge *)

(** [@requirement basincity_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [basincity_spec]. *)
Specification basincity_correct :
  forall (drone_count : N) (neighbour_lists : list (list N))
         (drone_count_int : uint)
           (neighbour_lists_arr : array (array uint)),
  valid_input drone_count neighbour_lists ->
  repr drone_count_int drone_count ->
  repr neighbour_lists_arr neighbour_lists ->
  exists output : bool,
    repr (basincity drone_count_int neighbour_lists_arr)
      output /\
    basincity_spec drone_count neighbour_lists output.

(** ** Complexity *)

(** [@hide] [basincity_cost] is the cost translation of [basincity] (the judge
    recomputes it and compares) ... *)
Complexity basincity_cost for basincity.

(** [@fold complexity bound] ... and runs in at most c1 * (5^k * (n + 1) + m) + c2 steps of the cost model on a valid input, k the number of drones, n the number of lines and m the total length of the neighbour lists ([sizes]): a search tree of depth at most k with at most five children per node (the vertex and its four neighbours), a linear scan per node; the 4^k of the binding branching rule is not stated, for two constants
    quantified before the inputs, on every valid input. [@requirement basincity_time_spec] *)
Specification basincity_time : exists c1 c2 : nat,
  forall (drone_count : N) (neighbour_lists : list (list N))
  (drone_count_int : uint)
  (neighbour_lists_arr : array (array uint)),
  valid_input drone_count neighbour_lists ->
  repr drone_count_int drone_count ->
  repr neighbour_lists_arr neighbour_lists ->
  basincity_time_spec c1 c2 (size drone_count_int) (size neighbour_lists_arr) (sizes neighbour_lists_arr) (cost2 basincity_cost drone_count_int neighbour_lists_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
