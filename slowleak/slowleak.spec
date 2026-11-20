(** * Slow Leak *)

(** ** Description *)

(** Ride a bicycle from school to home with a slowly leaking tire. A full
    tire lets you travel at most the given distance before it goes flat.
    Start with a full tire at school and refill it at any listed repair
    station along the way. Roads connect intersections in either direction.
    Find the shortest trip that reaches home without becoming stranded, or
    report that none exists. Reaching a station or home exactly as the tire
    goes flat is allowed.

    [@kattis slowleak]
    - Difficulty: 5.0
    - CPU time limit: 5 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 500$; road count: $1 \le m \le n(n-1)/2$, with no repeated pair.
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
                    It runs in at most c1 * (n^3 + m + t^2 + 1) + c2 steps
                    of the cost model on a valid input, m the number of
                    roads, t of refill stations, for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* Intersections are numbered 1 to
   intersection_count as in the statement; the roads are
   the parallel lists road_starts, road_ends,
   road_lengths (the m lines "i j k"). *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [e] in [l], or zero beyond the end. *)
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

(** [walk road_starts road_ends road_lengths start finish distance] means that a
    road walk from [start] to [finish] has total length [distance], using the
    network given by the parallel road lists. *)
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

(** The tire can be refilled at [intersection]: either the school or a listed repair
    station. *)
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

(** [distance] is the minimum length of a feasible trip from the school to home. *)
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
    The output is the shortest bicycle trip from school to home that respects
    the tire's range between refills, or [None] exactly when no such trip exists. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O(V^3+E+S^2+1)$ steps, where $V$ is the intersection count, $E$ the road count, and $S$ the number of repair stations. *)
Definition slowleak_time_spec (c1 c2 n_intersection_count n_road_starts n_stations steps : nat) : Prop :=
  (steps <= c1 * (n_intersection_count * n_intersection_count * n_intersection_count + n_road_starts + n_stations * n_stations + 1) + c2)%nat.

(** ** Interface *)

(** Find the shortest bicycle trip from school (intersection one) to home
    (the last intersection), refilling the leaking tire at repair stations.
    Start with a full tire; each stretch between refills or to home must be
    no longer than [tire_range].
    - Input [intersection_count]: Number of road intersections, including school and home.
    - Input [tire_range]: Distance a full tire lasts, with equality allowed.
    - Input [stations]: Intersections with tire-refilling stations.
    - Input [road_starts]: First endpoint of each undirected road.
    - Input [road_ends]: Second endpoint of each undirected road.
    - Input [road_lengths]: Length of each corresponding road.
    - Output [output]: [Some] shortest feasible trip length, or [None] exactly when home cannot be reached without becoming stranded. *)
Program slowleak :
  uint -> uint -> array uint -> array uint -> array uint ->
    array uint ->
  option uint.

(** [@example slowleak]
    - Sample: 1
    - Input [intersection_count]: 6
    - Input [tire_range]: 4
    - Input [stations]: [2; 5]
    - Input [road_starts]: [1; 1; 2; 3; 3; 4; 5]
    - Input [road_ends]: [2; 3; 3; 4; 5; 6; 6]
    - Input [road_lengths]: [4; 5; 3; 2; 1; 4; 4]
    - Output [output]: Some 12
*)

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

(** ** Complexity *)

(** [@hide] [slowleak_cost] is the cost translation of [slowleak] (the judge
    recomputes it and compares) ... *)
Complexity slowleak_cost for slowleak.

(** [@fold complexity bound] ... and runs in at most c1 * (n^3 + m + t^2 + 1) + c2 steps of the cost model on a valid input, m the number of roads, t of refill stations, for two constants
    quantified before the inputs, on every valid input. [@requirement slowleak_time_spec] *)
Specification slowleak_time : exists c1 c2 : nat,
  forall (intersection_count tire_range : N)
         (stations road_starts road_ends road_lengths : list N)
         (intersection_count_int tire_range_int : uint)
         (stations_arr road_starts_arr road_ends_arr road_lengths_arr
            : array uint),
  valid_input intersection_count tire_range stations road_starts road_ends
    road_lengths ->
  repr intersection_count_int intersection_count ->
  repr tire_range_int tire_range -> repr stations_arr stations ->
  repr road_starts_arr road_starts -> repr road_ends_arr road_ends ->
  repr road_lengths_arr road_lengths ->
  slowleak_time_spec c1 c2 (size intersection_count_int) (size road_starts_arr) (size stations_arr) (cost6 slowleak_cost intersection_count_int tire_range_int stations_arr road_starts_arr road_ends_arr road_lengths_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
