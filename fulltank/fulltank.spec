(** * Full Tank? *)

(** ** Description *)

(** Find the cheapest route in a road network with location-dependent fuel
    prices and a specified tank capacity. Start with an empty tank, buy
    whole fuel units, and consume one unit per unit of distance.

    [@kattis fulltank]
    - Difficulty: 4.1
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 1,000 vertices; at most 10,000 roads; 1 to 100 queries.
    - Fuel prices, road lengths and tank capacities are integers from 1 to
      100. *)

(** ** Examples *)

(** - Input convention: Graph size, fuel prices and weighted roads, followed by capacity-source-destination queries.
    - Output convention: One minimum fuel cost per query, or impossible if no feasible route exists. *)
(* Input:
5 5
10 10 20 12 13
0 1 9
0 2 8
1 2 1
1 3 11
2 3 7
2
10 0 3
20 1 4
Output:
170
impossible
*)

(** ** [@hide] Environment *)
(* @function        fulltank
   @signature       uint -> array uint -> array uint -> array uint ->
                    array uint -> array uint -> array uint -> array uint ->
                    array (option uint)
   @math_signature  N -> list N -> list N -> list N -> list N -> list N ->
                    list N -> list N -> list (option N)
   @summary         [fulltank city_count prices road_starts road_ends
                    road_lengths capacities starts goals]: city_count
                    cities with fuel prices prices, the two-way roads
                    road_starts_j -- road_ends_j of length road_lengths_j,
                    and the queries i (capacity capacities_i, start
                    starts_i, goal goals_i).  Answer i is Some price when
                    price is the price of the cheapest trip from starts_i
                    to goals_i with a car of tank capacity capacities_i
                    that starts empty, burns one unit of fuel per unit of
                    distance and buys whole units of fuel at the price of
                    the city it is in; None ("impossible") when there is
                    no such trip.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The roads (road_starts, road_ends, road_lengths) and the queries
    (capacities, starts, goals) are given as parallel lists, one per
    column of the input. The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The j-th element of l (0 beyond the end). *)
Definition get (l : list N) (j : N) : N :=
  nth (N.to_nat j) l 0.

(** Some road joins from_city and to_city (in either direction) and has
    length distance. *)
Definition road
  (road_starts road_ends road_lengths : list N)
    (from_city to_city distance : N) : Prop :=
  exists j, j < len road_starts /\
    ((get road_starts j = from_city /\ get road_ends j =
      to_city) \/
     (get road_starts j = to_city /\ get road_ends j =
       from_city)) /\
    distance = get road_lengths j.

(** [trip prices road_starts road_ends road_lengths capacity goal city
    fuel price]: standing in city with fuel units of fuel in the
    tank, the car can reach city goal paying price in total. At each
    city it buys bought >= 0 units at that city's price, never
    holding more than capacity, then drives a road it has the fuel
    for. *)
Inductive trip
  (prices road_starts road_ends road_lengths : list N)
    (capacity goal : N) : N -> N -> N -> Prop :=
  | trip_arrive : forall fuel,
      trip prices road_starts road_ends road_lengths
        capacity goal goal fuel
        0
  | trip_drive : forall city fuel bought next_city distance
    price,
      fuel + bought <= capacity ->
      road road_starts road_ends road_lengths city next_city
        distance ->
      distance <= fuel + bought ->
      trip prices road_starts road_ends road_lengths
        capacity goal next_city
        (fuel + bought - distance) price ->
      trip prices road_starts road_ends road_lengths
        capacity goal city fuel
        (get prices city * bought + price).

(** price is the least price over all trips from start, tank empty, to
    goal. *)
Definition cheapest
  (prices road_starts road_ends road_lengths : list N)
    (capacity start goal price : N) : Prop :=
  trip prices road_starts road_ends road_lengths capacity
    goal start 0
    price /\
  forall price',
    trip prices road_starts road_ends road_lengths capacity
      goal start 0
      price' ->
    price <= price'.

(** [@inside fulltank_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (city_count : N)
    (prices road_starts road_ends road_lengths capacities
      starts goals
       : list N) : Prop := {
  (* 1 <= n <= 1 000, the number of cities (city_count) *)
  vi_n : 1 <= city_count <= 1000;
  (* a line with n integers 1 <= p_i <= 100, the fuel
     price in city i (prices) *)
  vi_p_len : len prices = city_count;
  vi_p : Forall (fun price => 1 <= price <= 100) prices;
  (* 0 <= m <= 10 000, the number of roads *)
  vi_m : len road_starts <= 10000;
  (* m lines with three integers u, v, d (road_starts,
     road_ends, road_lengths) *)
  vi_v_len : len road_ends = len road_starts;
  vi_d_len : len road_lengths = len road_starts;
  (* 0 <= u, v < n *)
  vi_u : Forall (fun city => city < city_count) road_starts;
  vi_v : Forall (fun city => city < city_count) road_ends;
  (* 1 <= d <= 100, the length of the road *)
  vi_d : Forall (fun distance => 1 <= distance <= 100)
    road_lengths;
  (* 1 <= q <= 100, the number of queries *)
  vi_q : 1 <= len capacities <= 100;
  (* q lines with three integers c, s, e (capacities,
     starts, goals) *)
  vi_s_len : len starts = len capacities;
  vi_e_len : len goals = len capacities;
  (* 1 <= c <= 100, the fuel capacity of the vehicle *)
  vi_c : Forall (fun capacity => 1 <= capacity <= 100)
    capacities;
  (* s is the starting city, and e is the goal (cities are
     0 .. city_count-1) *)
  vi_s : Forall (fun city => city < city_count) starts;
  vi_e : Forall (fun city => city < city_count) goals;
}.

(** Some minimum feasible trip cost, or None exactly when no feasible trip exists. *)
Definition answer
  (prices road_starts road_ends road_lengths : list N)
    (capacity start goal : N) (result : option N) : Prop :=
  match result with
  | Some price =>
      cheapest prices road_starts road_ends road_lengths
        capacity start goal
        price
  | None =>
      ~ exists price,
          trip prices road_starts road_ends road_lengths
            capacity goal start
            0 price
  end.

(** ** Correctness *)

(** [@requirement]
    Each output entry is the minimum fuel cost of a feasible trip with the requested
    capacity and endpoints, starting with an empty tank, or None if no trip exists. *)
Definition fulltank_spec (city_count : N)
    (prices road_starts road_ends road_lengths capacities
      starts goals
       : list N)
    (output : list (option N)) : Prop :=
  len output = len capacities /\
  forall i, i < len capacities ->
    answer prices road_starts road_ends road_lengths (get
      capacities i)
      (get starts i) (get goals i) (nth (N.to_nat i) output
        None).

(** ** Interface *)

(** Find the cheapest route in a road network with location-dependent fuel prices and a
    specified tank capacity. Start with an empty tank, buy whole fuel units, and consume
    one unit per unit of distance.
    - Input [city_count]:
    - Input [prices]:
    - Input [road_starts]:
    - Input [road_ends]:
    - Input [road_lengths]:
    - Input [capacities]:
    - Input [starts]:
    - Input [goals]:
    - Output [output]: *)
Program fulltank : uint -> array uint -> array uint -> array
  uint ->
  array uint -> array uint -> array uint -> array uint ->
  array (option uint).

(** ** Bridge *)

(** [@requirement fulltank_spec] [@fold full correctness statement] On
    valid represented inputs, [fulltank] returns a represented
    output satisfying [fulltank_spec]. *)
Specification fulltank_correct :
  forall (city_count : N)
         (prices road_starts road_ends road_lengths
           capacities starts goals
            : list N)
         (city_count_int : uint)
         (prices_arr road_starts_arr road_ends_arr
           road_lengths_arr
            capacities_arr starts_arr goals_arr : array
              uint),
  valid_input city_count prices road_starts road_ends
    road_lengths
    capacities starts goals ->
  repr city_count_int city_count ->
    repr prices_arr prices ->
  repr road_starts_arr road_starts ->
    repr road_ends_arr road_ends ->
  repr road_lengths_arr road_lengths ->
    repr capacities_arr capacities ->
  repr starts_arr starts -> repr goals_arr goals ->
  exists output : list (option N),
    repr (fulltank city_count_int prices_arr road_starts_arr
      road_ends_arr
            road_lengths_arr capacities_arr starts_arr
              goals_arr)
      output /\
    fulltank_spec city_count prices road_starts road_ends
      road_lengths
      capacities starts goals output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
