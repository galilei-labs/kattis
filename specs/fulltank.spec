(* @function        fulltank
   @signature       uint -> array uint -> array uint -> array uint ->
                    array uint -> array uint -> array uint -> array uint ->
                    array (option uint)
   @math_signature  N -> list N -> list N -> list N -> list N -> list N ->
                    list N -> list N -> list (option N)
   @summary         [fulltank n p u v d c s e]: n cities with fuel prices p,
                    the two-way roads u_j -- v_j of length d_j, and the
                    queries i (capacity c_i, start s_i, goal e_i).  Answer i
                    is Some k when k is the price of the cheapest trip from
                    s_i to e_i with a car of tank capacity c_i that starts
                    empty, burns one unit of fuel per unit of distance and
                    buys whole units of fuel at the price of the city it is
                    in; None ("impossible") when there is no such trip.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* The roads (u, v, d) and the queries (c, s, e) are given as parallel
   lists, one per column of the input. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The j-th element of l (0 beyond the end). *)
Definition get (l : list N) (j : N) : N := nth (N.to_nat j) l 0.

(* Some road joins x and y (in either direction) and has length l. *)
Definition road (u v d : list N) (x y l : N) : Prop :=
  exists j, j < len u /\
    ((get u j = x /\ get v j = y) \/ (get u j = y /\ get v j = x)) /\
    l = get d j.

(* [trip p u v d cap g x f k]: standing in city x with f units of fuel in
   the tank, the car can reach city g paying k in total.  At each city it
   buys b >= 0 units at that city's price, never holding more than cap,
   then drives a road it has the fuel for. *)
Inductive trip (p u v d : list N) (cap g : N) : N -> N -> N -> Prop :=
  | trip_arrive : forall f, trip p u v d cap g g f 0
  | trip_drive : forall x f b y l k,
      f + b <= cap ->
      road u v d x y l -> l <= f + b ->
      trip p u v d cap g y (f + b - l) k ->
      trip p u v d cap g x f (get p x * b + k).

(* k is the least price over all trips from x, tank empty, to g. *)
Definition cheapest (p u v d : list N) (cap x g k : N) : Prop :=
  trip p u v d cap g x 0 k /\
  forall k', trip p u v d cap g x 0 k' -> k <= k'.

(* The statement's bounds. *)
Record valid_input (n : N) (p u v d c s e : list N) : Prop := {
  (* 1 <= n <= 1 000, the number of cities *)
  vi_n : 1 <= n <= 1000;
  (* a line with n integers 1 <= p_i <= 100, the fuel price in city i *)
  vi_p_len : len p = n;
  vi_p : Forall (fun x => 1 <= x <= 100) p;
  (* 0 <= m <= 10 000, the number of roads *)
  vi_m : len u <= 10000;
  (* m lines with three integers u, v, d *)
  vi_v_len : len v = len u;
  vi_d_len : len d = len u;
  (* 0 <= u, v < n *)
  vi_u : Forall (fun x => x < n) u;
  vi_v : Forall (fun x => x < n) v;
  (* 1 <= d <= 100, the length of the road *)
  vi_d : Forall (fun x => 1 <= x <= 100) d;
  (* 1 <= q <= 100, the number of queries *)
  vi_q : 1 <= len c <= 100;
  (* q lines with three integers c, s, e *)
  vi_s_len : len s = len c;
  vi_e_len : len e = len c;
  (* 1 <= c <= 100, the fuel capacity of the vehicle *)
  vi_c : Forall (fun x => 1 <= x <= 100) c;
  (* s is the starting city, and e is the goal (cities are 0 .. n-1) *)
  vi_s : Forall (fun x => x < n) s;
  vi_e : Forall (fun x => x < n) e;
}.

(* The answer to one query: the price of the cheapest trip, or None when
   there is no trip at all. *)
Definition answer (p u v d : list N) (cap x g : N) (r : option N) : Prop :=
  match r with
  | Some k => cheapest p u v d cap x g k
  | None => ~ exists k, trip p u v d cap g x 0 k
  end.

(* One answer per query, in order. *)
Definition fulltank_spec (n : N) (p u v d c s e : list N)
    (o : list (option N)) : Prop :=
  len o = len c /\
  forall i, i < len c ->
    answer p u v d (get c i) (get s i) (get e i) (nth (N.to_nat i) o None).

Program fulltank : uint -> array uint -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array uint ->
  array (option uint).

Specification fulltank_correct :
  forall (n : N) (p u v d c s e : list N)
         (xn : uint) (xp xu xv xd xc xs xe : array uint),
  valid_input n p u v d c s e ->
  repr xn n -> repr xp p -> repr xu u -> repr xv v -> repr xd d ->
  repr xc c -> repr xs s -> repr xe e ->
  exists o : list (option N),
    repr (fulltank xn xp xu xv xd xc xs xe) o /\
    fulltank_spec n p u v d c s e o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
