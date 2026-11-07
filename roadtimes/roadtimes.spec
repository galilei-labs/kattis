(** * Road Times *)

(** ** Description *)

(** Given a road network and observed journey durations, find the minimum
    and maximum possible duration of each queried journey. All journeys use
    their unique shortest-distance route, and each road has a fixed unknown
    speed between 30 and 60 km/h consistent with the observations.

    [@kattis roadtimes]
    - Difficulty: 6.8
    - CPU time limit: 5 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 30 vertices and at most 100 roads.
    - Road lengths from 1 to 1000 km; speeds from 30 to 60 km/h.
    - 1 to 100 observations and 1 to 100 queries; each pair has a unique
      shortest-distance route.
    - Some assignment of road speeds is consistent with all observations. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. Cities are 0 .. n-1; the deliveries and the
   queries are parallel lists, one per column of their
   input lines. A delivery time is a uint: the statement
   says integer, and a consistent delivery time
   (vi_consistent) is never negative. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element, for k < [len] l (0 outside, never
    relied on). *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** The j-th value of the i-th line of the matrix. *)
Definition entry (distances : list (list Z)) (i j : N) : Z
  :=
  nth (N.to_nat j) (nth (N.to_nat i) distances []) 0%Z.

(** There is a (one-way) [road] from city source to city
    destination. *)
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

(** cities lists the cities of a [route] from source to
    destination, consecutive ones joined by a [road]. *)
Inductive route (distances : list (list Z)) : N -> N -> list
  N -> Prop :=
| route_here : forall source, source < len distances ->
    route distances source source [source]
| route_step : forall source next destination cities,
    road distances source next -> route distances next
      destination cities ->
    route distances source destination (source :: cities).

(** The [distance] travelled along cities, in km. *)
Fixpoint distance (distances : list (list Z)) (cities :
  list N ) : Z :=
  match cities with
  | city :: (next :: _) as rest =>
      (entry distances city next + distance distances
        rest)%Z
  | _ => 0%Z
  end.

(** Shortest [route]. *)
Definition shortest_route distances source destination
  cities : Prop :=
  route distances source destination cities /\
  forall cities', route distances source destination cities'
    ->
    (distance distances cities <= distance distances
      cities')%Z.

(** Unique shortest [route]. *)
Definition unique_shortest_route distances source
  destination : Prop :=
  exists cities, shortest_route distances source destination
    cities /\
    forall cities', shortest_route distances source
      destination cities' ->
      cities' = cities.

(** The minutes needed to drive cities when [road] (city,
    next) is driven at speed city next km/h. *)
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

(** The trip from source to destination, along its
    minimum-[distance] [route], takes minutes minutes. *)
Definition trip_takes distances speed source destination
  (minutes : R)
    : Prop :=
  forall cities, shortest_route distances source destination
    cities ->
    duration distances speed cities = minutes.

(** Every delivery k took past_minutes_k minutes at the
    speed limits speed. *)
Definition matches_deliveries distances
    (past_sources past_destinations past_minutes : list N)
      speed : Prop :=
  forall k, k < len past_sources ->
    trip_takes distances speed (get_list_N past_sources k)
      (get_list_N past_destinations k)
      (IZR (Z.of_N (get_list_N past_minutes k))).

(** minutes minutes is a [possible] [duration] of the
    trip source -> destination. *)
Definition possible distances past_sources past_destinations
  past_minutes
    source destination (minutes : R) : Prop :=
  exists speed, speeds_ok distances speed /\
    matches_deliveries distances past_sources
      past_destinations
      past_minutes speed /\
    trip_takes distances speed source destination minutes.

(** Least [possible]. *)
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

(** Greatest [possible]. *)
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

(** approx is within absolute or relative error 10^-6 of
    exact. *)
Definition close (approx exact : R) : Prop :=
  (Rabs (approx - exact) <= / 1000000 \/
   Rabs (approx - exact) <= Rabs exact / 1000000)%R.

(** [@inside roadtimes_correct] Valid input. *)
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
     other distances are positive and at most 1 000 *)
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

(** [@requirement] [@short Find the least and greatest
    possible travel times for queried routes, given past
    deliveries and unknown road speeds between 30 and 60
    kilometres per hour.] One cell per query: the best
    low and high bounds on its travel time. *)
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

(** Find the least and greatest [possible] travel times
    for queried routes, given past deliveries and unknown
    [road] speeds between 30 and 60 kilometres per hour.
    - Input [distances]:
    - Input [past_sources]:
    - Input [past_destinations]:
    - Input [past_minutes]:
    - Input [query_sources]:
    - Input [query_destinations]:
    - Output [output]: *)
Program roadtimes : array (array sint) -> array uint ->
  array uint ->
  array uint -> array uint -> array uint -> array (float *
    float).

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
