(* @function        roadtimes
   @signature       array (array sint) -> array uint -> array uint ->
                    array uint -> array uint -> array uint ->
                    array (float * float)
   @math_signature  list (list Z) -> list N -> list N -> list N -> list N ->
                    list N -> list (R * R)
   @summary         [roadtimes dist rs rd rt qs qd]: dist is the n x n
                    matrix of road lengths in km (-1: no road), delivery k
                    went from rs_k to rd_k in rt_k minutes, query j asks
                    about the trip qs_j -> qd_j. Every road has an unknown
                    real speed limit in [30, 60] km/h and every trip drives
                    its unique minimum-distance route at those speeds. Cell
                    j of the result is the least and the greatest possible
                    duration in minutes of trip j over all speed limits
                    consistent with the deliveries, each within absolute or
                    relative error 10^-6. The harness prints qs_j qd_j first.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Cities are 0 .. n-1; the deliveries and the queries are
   parallel lists, one per column of their input lines.  A delivery time
   is a uint: the statement says integer, and a consistent delivery time
   (vi_consistent) is never negative. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* The j-th value of the i-th line of the matrix. *)
Definition entry (dist : list (list Z)) (i j : N) : Z :=
  nth (N.to_nat j) (nth (N.to_nat i) dist []) 0%Z.

(* There is a (one-way) road from city i to city j. *)
Definition road (dist : list (list Z)) (i j : N) : Prop :=
  i < len dist /\ j < len dist /\ (0 < entry dist i j)%Z.

(* The number of roads: the positive values of the matrix. *)
Definition road_count (dist : list (list Z)) : N :=
  len (filter (fun x => Z.ltb 0 x) (concat dist)).

(* p lists the cities of a route from s to d, consecutive ones joined by a
   road. *)
Inductive route (dist : list (list Z)) : N -> N -> list N -> Prop :=
| route_here : forall s, s < len dist -> route dist s s [s]
| route_step : forall s m d p,
    road dist s m -> route dist m d p -> route dist s d (s :: p).

(* The distance travelled along p, in km. *)
Fixpoint distance (dist : list (list Z)) (p : list N) : Z :=
  match p with
  | i :: (j :: _) as tl => (entry dist i j + distance dist tl)%Z
  | _ => 0%Z
  end.

Definition shortest_route dist s d p : Prop :=
  route dist s d p /\
  forall p', route dist s d p' -> (distance dist p <= distance dist p')%Z.

Definition unique_shortest_route dist s d : Prop :=
  exists p, shortest_route dist s d p /\
            forall p', shortest_route dist s d p' -> p' = p.

(* The minutes needed to drive p when road (i, j) is driven at v i j km/h. *)
Fixpoint duration dist (v : N -> N -> R) (p : list N) : R :=
  match p with
  | i :: (j :: _) as tl =>
      (60 * IZR (entry dist i j) / v i j + duration dist v tl)%R
  | _ => 0%R
  end.

(* Every road has a speed limit between 30 and 60 km/h. *)
Definition speeds_ok dist (v : N -> N -> R) : Prop :=
  forall i j, road dist i j -> (30 <= v i j <= 60)%R.

(* The trip from s to d, along its minimum-distance route, takes t minutes. *)
Definition trip_takes dist v s d (t : R) : Prop :=
  forall p, shortest_route dist s d p -> duration dist v p = t.

(* Every delivery k took rt_k minutes at the speed limits v. *)
Definition matches_deliveries dist (rs rd rt : list N) v : Prop :=
  forall k, k < len rs ->
    trip_takes dist v (get_list_N rs k) (get_list_N rd k)
               (IZR (Z.of_N (get_list_N rt k))).

(* t minutes is a possible duration of the trip s -> d. *)
Definition possible dist rs rd rt s d (t : R) : Prop :=
  exists v, speeds_ok dist v /\ matches_deliveries dist rs rd rt v /\
            trip_takes dist v s d t.

Definition least_possible dist rs rd rt s d (t : R) : Prop :=
  possible dist rs rd rt s d t /\
  forall t', possible dist rs rd rt s d t' -> (t <= t')%R.

Definition greatest_possible dist rs rd rt s d (t : R) : Prop :=
  possible dist rs rd rt s d t /\
  forall t', possible dist rs rd rt s d t' -> (t' <= t)%R.

(* y is within absolute or relative error 10^-6 of t. *)
Definition close (y t : R) : Prop :=
  (Rabs (y - t) <= / 1000000 \/ Rabs (y - t) <= Rabs t / 1000000)%R.

Record valid_input (dist : list (list Z)) (rs rd rt qs qd : list N) : Prop := {
  (* an integer n (1 <= n <= 30) indicating the number of cities *)
  vi_n : 1 <= len dist <= 30;
  (* n lines each containing n integers *)
  vi_rows : Forall (fun row => len row = len dist) dist;
  (* the distance from any city to itself is always 0 *)
  vi_diag : forall i, i < len dist -> entry dist i i = 0%Z;
  (* a value of -1 indicates there is no road ...; all other distances are
     positive and at most 1 000 *)
  vi_dist : forall i j, i < len dist -> j < len dist -> i <> j ->
    entry dist i j = (-1)%Z \/ (1 <= entry dist i j <= 1000)%Z;
  (* there are at most 100 roads *)
  vi_roads : road_count dist <= 100;
  (* an integer r (1 <= r <= 100) indicating the number of previously
     executed routes; r lines each contain s, d and t *)
  vi_r : 1 <= len rs <= 100;
  vi_rd : len rd = len rs;
  vi_rt : len rt = len rs;
  (* an integer q (1 <= q <= 100) indicating the number of queries; q lines
     each contain s and d *)
  vi_q : 1 <= len qs <= 100;
  vi_qd : len qd = len qs;
  (* s and d are cities, numbered 0 to n-1 *)
  vi_r_cities : forall k, k < len rs ->
    get_list_N rs k < len dist /\ get_list_N rd k < len dist;
  vi_q_cities : forall k, k < len qs ->
    get_list_N qs k < len dist /\ get_list_N qd k < len dist;
  (* for each of the r+q source/destination pairs in the input there is a
     unique minimum-distance route *)
  vi_r_unique : forall k, k < len rs ->
    unique_shortest_route dist (get_list_N rs k) (get_list_N rd k);
  (* idem, for the queries *)
  vi_q_unique : forall k, k < len qs ->
    unique_shortest_route dist (get_list_N qs k) (get_list_N qd k);
  (* the deliveries were performed: trucks take the minimum-distance route
     at each road's speed limit, between 30 and 60 km/h, so some speed
     limits explain all the delivery times *)
  vi_consistent : exists v, speeds_ok dist v /\
    matches_deliveries dist rs rd rt v;
}.

(* One cell per query: the best low and high bounds on its travel time. *)
Definition roadtimes_spec (dist : list (list Z)) (rs rd rt qs qd : list N)
    (o : list (R * R)) : Prop :=
  len o = len qs /\
  forall j, j < len qs ->
    exists lo hi,
      least_possible dist rs rd rt (get_list_N qs j) (get_list_N qd j) lo /\
      greatest_possible dist rs rd rt (get_list_N qs j) (get_list_N qd j) hi /\
      close (fst (nth (N.to_nat j) o (0, 0)%R)) lo /\
      close (snd (nth (N.to_nat j) o (0, 0)%R)) hi.

Program roadtimes : array (array sint) -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array (float * float).

Specification roadtimes_correct :
  forall (dist : list (list Z)) (rs rd rt qs qd : list N)
         (xdist : array (array sint))
         (xrs xrd xrt xqs xqd : array uint),
    valid_input dist rs rd rt qs qd ->
    repr xdist dist -> repr xrs rs -> repr xrd rd -> repr xrt rt ->
    repr xqs qs -> repr xqd qd ->
    exists o : list (R * R),
      repr (roadtimes xdist xrs xrd xrt xqs xqd) o /\
      roadtimes_spec dist rs rd rt qs qd o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
