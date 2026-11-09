(** * Slow Leak *)

(** ** Description *)

(** Find the shortest route in a weighted road network subject to a maximum
    distance between refills at designated vertices. Start with a full
    supply, or report that no route is possible.

    [@kattis slowleak]
    - Difficulty: 5.0
    - CPU time limit: 5 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 500$; $1$ to $n(n-1)/2$ roads, with no repeated pair.
    - Refill vertices are distinct and exclude the endpoints.
    - Positive road lengths, travel range and any feasible minimum total
      distance are below $2^{31}$. *)

(** ** Examples *)

(** - Input convention: Vertex/edge/refill counts and distance limit, refill vertices, then weighted undirected edges.
    - Output convention: Minimum feasible route length from vertex 1 to n, or stuck. *)
(* Input:
6 7 2 4
2 5
1 2 4
1 3 5
2 3 3
3 4 2
3 5 1
4 6 4
5 6 4
Output:
12
*)

(** ** [@hide] Environment *)

(* @function        slowleak
   @signature       uint -> uint -> array uint -> array uint -> array uint ->
                    array uint -> option uint
   @math_signature  N -> N -> list N -> list N -> list N -> list N -> option N
   @summary         [slowleak intersection_count tire_range stations
                    road_starts road_ends road_lengths] is the length of the
                    shortest trip from intersection 1 (school) to
                    intersection intersection_count (home) along the roads
                    road_starts.[e] -- road_ends.[e] of length
                    road_lengths.[e], ridden in either direction, in which
                    the distance ridden since the last refill never exceeds
                    tire_range; the tire is refilled at the school and at
                    the repair stations.  None ("stuck") when no such trip
                    exists.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. Intersections are numbered 1 to
   intersection_count as in the statement; the roads are
   the parallel lists road_starts, road_ends,
   road_lengths (the m lines "i j k"). *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The e-th element of l, e counted from 0. *)
Definition get (l : list N) (e : N) : N :=
  nth (N.to_nat e) l 0.

(** Some [road] joins start and finish with length
    distance, travelled in either direction. *)
Definition road
  (road_starts road_ends road_lengths : list N)
    (start finish distance : N) : Prop :=
  exists e, e < len road_starts /\ get road_lengths e =
    distance /\
    ((get road_starts e = start /\ get road_ends e = finish)
      \/
     (get road_starts e = finish /\ get road_ends e = start)
       ).

(** [walk start finish distance]: a [walk] along roads
    from start to finish of total length distance. *)
Inductive walk (road_starts road_ends road_lengths : list N)
    : N -> N -> N -> Prop :=
  | walk_nil : forall start,
      walk road_starts road_ends road_lengths start start 0
  | walk_cons : forall start next finish step_length
    rest_length,
      road road_starts road_ends road_lengths start next
        step_length ->
      walk road_starts road_ends road_lengths next finish
        rest_length ->
      walk road_starts road_ends road_lengths start finish
        (step_length + rest_length).

(** The tire can be refilled at intersection: the school
    or a repair station. *)
Definition refill (stations : list N) (intersection : N) :
  Prop :=
  intersection = 1 \/ In intersection stations.

(** [trip start distance]: leaving start with a full
    tire, home ([intersection_count]) is reached after a
    total length distance, each stretch between two
    refills, or from the last [refill] to home, being at
    most [tire_range] (arriving exactly as the tire goes
    flat is fine). *)
Inductive trip (intersection_count tire_range : N)
    (stations road_starts road_ends road_lengths : list N)
    : N -> N -> Prop :=
  | trip_home : forall start distance,
      walk road_starts road_ends road_lengths start
        intersection_count
        distance ->
      distance <= tire_range ->
      trip intersection_count tire_range stations
        road_starts road_ends
        road_lengths start distance
  | trip_refill : forall start station distance distance',
      walk road_starts road_ends road_lengths start station
        distance ->
      distance <= tire_range -> refill stations station ->
      trip intersection_count tire_range stations
        road_starts road_ends
        road_lengths station distance' ->
      trip intersection_count tire_range stations
        road_starts road_ends
        road_lengths start (distance + distance').

(** distance is the length of a [trip] from the school,
    and no such [trip] is shorter. *)
Definition shortest (intersection_count tire_range : N)
    (stations road_starts road_ends road_lengths : list N)
      (distance : N)
    : Prop :=
  trip intersection_count tire_range stations road_starts
    road_ends
    road_lengths 1 distance /\
  forall distance',
    trip intersection_count tire_range stations road_starts
      road_ends
      road_lengths 1 distance' ->
    distance <= distance'.

(** [@inside slowleak_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (intersection_count tire_range : N)
    (stations road_starts road_ends road_lengths : list N) :
      Prop := {
  (* 2 <= n <= 500 *)
  vi_n : 2 <= intersection_count <= 500;
  (* 0 < m <= n(n-1)/2 *)
  vi_m : 0 < len road_starts
           <= intersection_count * (intersection_count - 1)
            / 2;
  (* the next m lines each hold three integers i, j, k *)
  vi_rj : len road_ends = len road_starts;
  vi_rk : len road_lengths = len road_starts;
  (* 0 < t < n *)
  vi_t : 0 < len stations < intersection_count;
  (* 0 < d < 2^31 *)
  vi_d : 0 < tire_range < 2 ^ 31;
  (* the t stations have values between 2 and n-1,
     inclusive *)
  vi_st : Forall (fun station => 2 <= station <=
    intersection_count - 1)
            stations;
  (* all integers on this line are unique *)
  vi_st_unique : NoDup stations;
  (* 1 <= i < j <= n *)
  vi_ij : Forall2 (fun start finish =>
                     1 <= start /\ start < finish <=
            intersection_count)
            road_starts road_ends;
  (* 0 < k < 2^31 *)
  vi_k : Forall
    (fun road_length => 0 < road_length < 2 ^ 31)
    road_lengths;
  (* there is at most one road between any two
     intersections *)
  vi_simple : NoDup (combine road_starts road_ends);
  (* if the trip is possible, the minimum distance D
     satisfies 0 < D < 2^31 *)
  vi_answer : forall distance,
    shortest intersection_count tire_range stations
      road_starts road_ends
      road_lengths distance ->
    0 < distance < 2 ^ 31;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the minimum length of a route satisfying the refill-distance
    constraint, or None exactly when no feasible route exists. *)
Definition slowleak_spec
  (intersection_count tire_range : N)
  (stations road_starts road_ends road_lengths : list N)
  (output : option N)
  : Prop :=
  match output with
  | Some distance =>
      shortest intersection_count tire_range stations
        road_starts road_ends
        road_lengths distance
  | None =>
      forall distance,
        ~ trip intersection_count tire_range stations
          road_starts road_ends
            road_lengths 1 distance
  end.

(** ** Interface *)

(** Find the shortest route in a weighted road network subject to a maximum distance between
    refills at designated vertices. Start with a full supply, or report that no route is
    possible.
    - Input [intersection_count]: Number of vertices in the road network.
    - Input [tire_range]: Maximum distance that can be traveled between refills.
    - Input [stations]: Vertices at which the supply can be refilled.
    - Input [road_starts]: First endpoint of each undirected road.
    - Input [road_ends]: Second endpoint of each undirected road.
    - Input [road_lengths]: Length of each corresponding road.
    - Output [output]: The output is the minimum length of a route satisfying the refill-distance constraint, or None exactly when no feasible route exists. *)
Program slowleak :
  uint -> uint -> array uint -> array uint -> array uint ->
    array uint ->
  option uint.

(** ** Bridge *)

(** [@requirement slowleak_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [slowleak_spec]. *)
Specification slowleak_correct :
  forall (intersection_count tire_range : N)
         (stations road_starts road_ends road_lengths :
           list N )
         (intersection_count_int tire_range_int : uint)
         (stations_arr road_starts_arr road_ends_arr
           road_lengths_arr
            : array uint),
  valid_input intersection_count tire_range stations
    road_starts road_ends
    road_lengths ->
  repr intersection_count_int intersection_count ->
  repr tire_range_int tire_range -> repr stations_arr
    stations ->
  repr road_starts_arr road_starts -> repr road_ends_arr
    road_ends ->
  repr road_lengths_arr road_lengths ->
  exists output : option N,
    repr (slowleak intersection_count_int tire_range_int
      stations_arr
            road_starts_arr road_ends_arr road_lengths_arr)
            output /\
    slowleak_spec intersection_count tire_range stations
      road_starts road_ends
      road_lengths output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
