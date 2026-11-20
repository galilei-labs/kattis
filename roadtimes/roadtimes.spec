(** * Road Times *)

(** ** Description *)

(** Given a road network and observed journey durations, find the minimum
    and maximum possible duration of each queried journey. All journeys use
    their unique shortest-distance route, and each road has a fixed unknown
    speed between 30 and 60 km/h consistent with the observations.

    [@kattis roadtimes]
    - Difficulty: 6.9
    - CPU time limit: 5 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 30$ and at most $100$ roads.
    - Road lengths: $1 \le d_i \le 10^{3}$ km; speeds: $30 \le v_i \le 60$ km/h.
    - Observation count: $1 \le r \le 100$ and Query count: $1 \le q \le 100$; each pair has a unique
      shortest-distance route.
    - Some assignment of road speeds is consistent with all observations. *)

(** ** Examples *)

(** - Input convention: Distance matrix, observed source-destination-duration triples, then source-destination queries.
    - Output convention: Query endpoints followed by the tight lower and upper travel-time bounds. *)
(* Input:
3
0 50 -1
55 0 40
-1 40 0
1
0 2 120
3
0 1
1 2
1 0
Output:
0 1 50.0 80.0
1 2 40.0 70.0
1 0 55.0 110.0
*)

(** ** [@hide] Environment *)

(* @function        roadtimes
   @signature       array (array sint) -> array uint -> array uint ->
                    array uint -> array uint -> array uint ->
                    array (float * float)
   @math_signature  list (list Z) -> list N -> list N -> list N -> list N ->
                    list N -> list (R * R)
   @summary         [roadtimes distances past_sources past_destinations
                    past_minutes query_sources query_destinations]:
                    distances is the n x n matrix of road lengths in km
                    (-1: no road), delivery k went from past_sources_k to
                    past_destinations_k in past_minutes_k minutes, query j
                    asks about the trip query_sources_j ->
                    query_destinations_j. Every road has an unknown real
                    speed limit in [30, 60] km/h and every trip drives its
                    unique minimum-distance route at those speeds. Cell j
                    of the result is the least and the greatest possible
                    duration in minutes of trip j over all speed limits
                    consistent with the deliveries, each within absolute or
                    relative error 10^-6. The harness prints
                    query_sources_j query_destinations_j first.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Cities are 0 .. n-1; the deliveries and the
   queries are parallel lists, one per column of their
   input lines. A delivery time is a uint: the statement
   says integer, and a consistent delivery time
   (vi_consistent) is never negative. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** The matrix entry at zero-based row [i] and column [j]. *)
Definition entry (distances : list (list Z)) (i j : N) : Z
  :=
  nth (N.to_nat j) (nth (N.to_nat i) distances []) 0%Z.

(** An input road leads from [source] to [destination]. Roads are directed. *)
Definition road (distances : list (list Z))
  (source destination : N)
    : Prop :=
  source < len distances /\ destination < len distances /\
  (0 < entry distances source destination)%Z.

(** The number of roads: the positive values of the
    matrix. *)
Definition road_count (distances : list (list Z)) : N :=
  len (filter (fun value => Z.ltb 0 value) (concat
    distances)).

(** [route distances source destination cities] means that [cities] lists a
    directed route from [source] to [destination] in the road matrix [distances],
    with a road between every consecutive pair. *)
Inductive route (distances : list (list Z)) : N -> N -> list
  N -> Prop :=
| route_here : forall source, source < len distances ->
    route distances source source [source]
| route_step : forall source next destination cities,
    road distances source next -> route distances next
      destination cities ->
    route distances source destination (source :: cities).

(** The total road distance along [cities], in kilometres. *)
Fixpoint distance (distances : list (list Z)) (cities :
  list N ) : Z :=
  match cities with
  | city :: (next :: _) as rest =>
      (entry distances city next + distance distances
        rest)%Z
  | _ => 0%Z
  end.

(** The route has minimum total road distance between its endpoints. *)
Definition shortest_route distances source destination
  cities : Prop :=
  route distances source destination cities /\
  forall cities', route distances source destination cities'
    ->
    (distance distances cities <= distance distances
      cities')%Z.

(** Exactly one route has minimum total road distance between the endpoints. *)
Definition unique_shortest_route distances source
  destination : Prop :=
  exists cities, shortest_route distances source destination
    cities /\
    forall cities', shortest_route distances source
      destination cities' ->
      cities' = cities.

(** The journey duration along [cities], in minutes, using the road speeds supplied
    by [speed] in kilometres per hour. *)
Fixpoint duration distances (speed : N -> N -> R)
  (cities : list N) : R :=
  match cities with
  | city :: (next :: _) as rest =>
      (60 * IZR (entry distances city next) / speed city
        next
       + duration distances speed rest)%R
  | _ => 0%R
  end.

(** Every [road] has a speed limit between 30 and 60
    km/h. *)
Definition speeds_ok distances (speed : N -> N -> R) : Prop
  :=
  forall source destination, road distances source
    destination ->
    (30 <= speed source destination <= 60)%R.

(** Every minimum-distance route from [source] to [destination] takes [minutes]
    minutes at the supplied road speeds. Valid inputs require the minimum-distance
    route to be unique. *)
Definition trip_takes distances speed source destination
  (minutes : R)
    : Prop :=
  forall cities, shortest_route distances source destination
    cities ->
    duration distances speed cities = minutes.

(** The road speeds reproduce every observed delivery duration in [past_minutes]. *)
Definition matches_deliveries distances
    (past_sources past_destinations past_minutes : list N)
      speed : Prop :=
  forall k, k < len past_sources ->
    trip_takes distances speed (get_list_N past_sources k)
      (get_list_N past_destinations k)
      (IZR (Z.of_N (get_list_N past_minutes k))).

(** Some road speeds satisfying the limits and all observed deliveries give the
    queried journey duration [minutes]. *)
Definition possible distances past_sources past_destinations
  past_minutes
    source destination (minutes : R) : Prop :=
  exists speed, speeds_ok distances speed /\
    matches_deliveries distances past_sources
      past_destinations
      past_minutes speed /\
    trip_takes distances speed source destination minutes.

(** [minutes] is an attainable journey duration, and no consistent choice of road
    speeds gives a smaller duration. *)
Definition least_possible distances past_sources
  past_destinations
    past_minutes source destination (minutes : R) : Prop :=
  possible distances past_sources past_destinations
    past_minutes
    source destination minutes /\
  forall minutes', possible distances past_sources
    past_destinations
    past_minutes source destination minutes' -> (minutes <=
      minutes')%R.

(** [minutes] is an attainable journey duration, and no consistent choice of road
    speeds gives a larger duration. *)
Definition greatest_possible distances past_sources
  past_destinations
    past_minutes source destination (minutes : R) : Prop :=
  possible distances past_sources past_destinations
    past_minutes
    source destination minutes /\
  forall minutes', possible distances past_sources
    past_destinations
    past_minutes source destination minutes' -> (minutes' <=
      minutes)%R.

(** [approx] is within absolute or relative error $10^{-6}$ of [exact]. *)
Definition close (approx exact : R) : Prop :=
  (Rabs (approx - exact) <= / 1000000 \/
   Rabs (approx - exact) <= Rabs exact / 1000000)%R.

(** [@inside roadtimes_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (distances : list (list Z))
    (past_sources past_destinations past_minutes : list N)
    (query_sources query_destinations : list N) : Prop := {
  (* an integer n (1 <= n <= 30) indicating the number of
     cities *)
  vi_n : 1 <= len distances <= 30;
  (* n lines each containing n integers *)
  vi_rows : Forall (fun row => len row = len distances)
    distances;
  (* the distance from any city to itself is always 0 *)
  vi_diag : forall i, i < len distances -> entry distances i
    i = 0%Z;
  (* a value of -1 indicates there is no road ...; all
     other distances are positive and at most 10^3 *)
  vi_dist : forall i j, i < len distances -> j < len
    distances -> i <> j ->
    entry distances i j = (-1)%Z \/
      (1 <= entry distances i j <= 1000)%Z;
  (* there are at most 100 roads *)
  vi_roads : road_count distances <= 100;
  (* an integer r (1 <= r <= 100) indicating the number
     of previously executed routes; r lines each contain
     s, d and t *)
  vi_r : 1 <= len past_sources <= 100;
  vi_rd : len past_destinations = len past_sources;
  vi_rt : len past_minutes = len past_sources;
  (* an integer q (1 <= q <= 100) indicating the number
     of queries; q lines each contain s and d *)
  vi_q : 1 <= len query_sources <= 100;
  vi_qd : len query_destinations = len query_sources;
  (* s and d are cities, numbered 0 to n-1 *)
  vi_r_cities : forall k, k < len past_sources ->
    get_list_N past_sources k < len distances /\
    get_list_N past_destinations k < len distances;
  vi_q_cities : forall k, k < len query_sources ->
    get_list_N query_sources k < len distances /\
    get_list_N query_destinations k < len distances;
  (* for each of the r+q source/destination pairs in the
     input there is a unique minimum-distance route *)
  vi_r_unique : forall k, k < len past_sources ->
    unique_shortest_route distances
      (get_list_N past_sources k)
      (get_list_N past_destinations k);
  (* idem, for the queries *)
  vi_q_unique : forall k, k < len query_sources ->
    unique_shortest_route distances
      (get_list_N query_sources k)
      (get_list_N query_destinations k);
  (* the deliveries were performed: trucks take the
     minimum-distance route at each road's speed limit,
     between 30 and 60 km/h, so some speed limits explain
     all the delivery times *)
  vi_consistent : exists speed, speeds_ok distances speed /\
    matches_deliveries distances past_sources
      past_destinations
      past_minutes speed;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry approximates the tight minimum and maximum travel times consistent
    with all observations and speed constraints, within the specified tolerance. *)
Definition roadtimes_spec
  (distances : list (list Z))
  (past_sources past_destinations past_minutes : list N)
  (query_sources query_destinations : list N)
  (output : list (R * R))
  : Prop :=
  len output = len query_sources /\
  forall j, j < len query_sources ->
    exists least greatest,
      least_possible distances past_sources
        past_destinations past_minutes
        (get_list_N query_sources j) (get_list_N
          query_destinations j)
        least /\
      greatest_possible distances past_sources
        past_destinations
        past_minutes
        (get_list_N query_sources j) (get_list_N
          query_destinations j)
        greatest /\
      close (fst (nth (N.to_nat j) output (0, 0)%R)) least
        /\
      close (snd (nth (N.to_nat j) output (0, 0)%R))
        greatest.

(** ** Interface *)

(** Given a road network and observed journey durations, find the minimum and maximum
    possible duration of each queried journey. All journeys use their unique
    shortest-distance route, and each road has a fixed unknown speed between 30 and 60 km/h
    consistent with the observations.
    - Input [distances]: Square matrix with zero-based source rows and destination columns. Positive entries are directed road lengths in kilometres; -1 denotes no road and diagonal entries are zero.
    - Input [past_sources]: Zero-based starting city of each observed journey.
    - Input [past_destinations]: Zero-based destination city of each observed journey.
    - Input [past_minutes]: Recorded duration of each journey, in minutes.
    - Input [query_sources]: Zero-based starting city of each queried journey.
    - Input [query_destinations]: Zero-based destination city of each queried journey.
    - Output [output]: A pair (minimum, maximum) of travel times in minutes per query, in query order, approximating the tight bounds consistent with all observations within the specified tolerance. *)
Program roadtimes : array (array sint) -> array uint ->
  array uint ->
  array uint -> array uint -> array uint -> array (float *
    float).

(** [@example roadtimes]
    - Sample: 1
    - Input [distances]: [[0; 50; -1]; [55; 0; 40]; [-1; 40; 0]]%Z
    - Input [past_sources]: [0]
    - Input [past_destinations]: [2]
    - Input [past_minutes]: [120]
    - Input [query_sources]: [0; 1; 1]
    - Input [query_destinations]: [1; 2; 0]
    - Output [output]: [(50, 80); (40, 70); (55, 110)]%R
*)

(** ** Bridge *)

(** [@requirement roadtimes_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [roadtimes_spec]. *)
Specification roadtimes_correct :
  forall (distances : list (list Z))
         (past_sources past_destinations past_minutes :
           list N )
         (query_sources query_destinations : list N)
         (distances_arr : array (array sint))
         (past_sources_arr past_destinations_arr
           past_minutes_arr : array uint )
         (query_sources_arr query_destinations_arr :
           array uint ),
    valid_input distances past_sources past_destinations
      past_minutes
      query_sources query_destinations ->
    repr distances_arr distances ->
    repr past_sources_arr past_sources ->
    repr past_destinations_arr past_destinations ->
    repr past_minutes_arr past_minutes ->
    repr query_sources_arr query_sources ->
    repr query_destinations_arr query_destinations ->
    exists output : list (R * R),
      repr (roadtimes distances_arr past_sources_arr
        past_destinations_arr
              past_minutes_arr query_sources_arr
            query_destinations_arr)
        output /\
      roadtimes_spec distances past_sources
        past_destinations past_minutes
        query_sources query_destinations output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
