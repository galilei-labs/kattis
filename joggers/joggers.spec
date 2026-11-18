(** * Chicken Joggers *)

(** ** Description *)

(** Trails connect intersections in a tree, with the campus at intersection
    1. Joggers start and finish at the campus, running exactly the specified
    distance; they may turn around inside a trail. Add the fewest lamps so
    every trail that any such jogger can use has a lamp at one of its ends.

    [@kattis joggers]
    - Difficulty: 5.2
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $2 \le n \le 5 \times 10^{4}$ intersections forming a tree; trail lengths: $1 \le d_i \le 100$ metres.
    - Jogging distance: $1 \le S \le 10^{4}$ metres; at most one existing lamp per intersection. *)

(** ** Examples *)

(** - Input convention: Intersection count and jogging distance, trail endpoints and lengths, then the count and intersection numbers of existing lamps.
    - Output convention: The minimum number of additional lamps. *)
(* Input:
5 6
1 2 1
1 3 1
4 3 3
3 5 2
1
1
Output:
1
*)

(** ** [@hide] Environment *)
(* @function        joggers
   @signature       uint -> uint -> array uint -> array uint -> array uint ->
                    array uint -> uint
   @math_signature  N -> N -> list N -> list N -> list N -> list N -> N
   @summary         [joggers intersection_count jog_distance trail_starts
                    trail_ends trail_lengths lamps]: the woods have
                    intersections 1..intersection_count, the campus is 1,
                    trail j joins trail_starts_j and trail_ends_j and is
                    trail_lengths_j metres long, and lamps already stand at
                    the intersections listed in lamps. A jogger runs
                    exactly jog_distance metres from the campus back to
                    the campus, turning around anywhere, even inside a
                    trail. The result is the least number of new lamps,
                    placed at intersections, such that every trail some
                    jogger may run on has a lamp at one of its two ends.
                    It runs in at most c1 * (n + t + l + 1) + c2 steps of
                    the cost model on a valid input, n the number of
                    intersections, t of trails and l of lamps (one
                    traversal, then the tree dynamic programming), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Reals.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** Embed the natural number [value] in the real numbers. *)
Definition rN (value : N) : R := IZR (Z.of_N value).

(** [intersection] is a valid one-based intersection number. *)
Definition inter
  (intersection_count intersection : N) : Prop :=
  1 <= intersection <= intersection_count.

(** Following the trails [trails] in order leads from [from_node] to
    [to_node]. *)
Fixpoint chain (trail_starts trail_ends : list N)
  (from_node : N)
    (trails : list N) (to_node : N) : Prop :=
  match trails with
  | [] => from_node = to_node
  | j :: trails' => j < len trail_starts /\
      ((get trail_starts j = from_node /\
        chain trail_starts trail_ends (get trail_ends j)
          trails' to_node) \/
       (get trail_ends j = from_node /\
        chain trail_starts trail_ends (get trail_starts j)
          trails' to_node))
  end.

(** A route from [from_node] to [to_node]: adjacent trails, none used
    twice. *)
Definition route (trail_starts trail_ends : list N)
  (from_node : N)
    (trails : list N) (to_node : N) : Prop :=
  chain trail_starts trail_ends from_node trails to_node /\
    NoDup trails.

(** A position on a trail: its zero-based trail index and the distance in metres
    from that trail's first endpoint. *)
Definition place : Type := (N * R)%type.

(** [spot] names an existing trail and a distance between zero and that trail's
    length, inclusive. *)
Definition in_woods (trail_lengths : list N)
  (spot : place) : Prop :=
  fst spot < len trail_lengths /\
  (0 <= snd spot <= rN (get trail_lengths (fst spot)))%R.

(** The place [spot] is the intersection [intersection]. *)
Definition at_inter
  (trail_starts trail_ends trail_lengths : list N)
    (spot : place) (intersection : N) : Prop :=
  (snd spot = 0%R /\ get trail_starts (fst spot) =
    intersection) \/
  (snd spot = rN (get trail_lengths (fst spot)) /\
   get trail_ends (fst spot) = intersection).

(** One leg of a run goes straight along one trail, or switches trails
    at an intersection; its length is the distance covered on the
    trail. *)
Definition leg_ok
  (trail_starts trail_ends trail_lengths : list N)
    (spot next_spot : place) : Prop :=
  fst spot = fst next_spot \/
  exists intersection,
    at_inter trail_starts trail_ends trail_lengths spot
      intersection /\
    at_inter trail_starts trail_ends trail_lengths next_spot
      intersection.

(** The distance between two positions on the same trail; zero for positions on
    different trails. A valid change of trails occurs at a shared intersection. *)
Definition leg_len (spot next_spot : place) : R :=
  if fst spot =? fst next_spot then Rabs (snd spot - snd
    next_spot)
  else 0%R.

(** Every consecutive pair of positions, beginning at [spot] and continuing through
    [turns], satisfies [leg_ok]. *)
Fixpoint legs_ok
  (trail_starts trail_ends trail_lengths : list N)
    (spot : place) (turns : list place) : Prop :=
  match turns with
  | [] => True
  | next_spot :: turns' =>
      leg_ok trail_starts trail_ends trail_lengths spot
        next_spot /\
      legs_ok trail_starts trail_ends trail_lengths
        next_spot turns'
  end.

(** The total length of the legs from [spot] through [turns], computed using
    [leg_len]. *)
Fixpoint run_len (spot : place) (turns : list place) : R :=
  match turns with
  | [] => 0%R
  | next_spot :: turns' =>
      (leg_len spot next_spot + run_len next_spot turns')%R
  end.

(** A jogger's run: from [spot] through the turning points [turns],
    starting and finishing at the campus (intersection 1), exactly [jog_distance]
    metres long. *)
Definition jog
  (trail_starts trail_ends trail_lengths : list N)
    (jog_distance : N) (spot : place) (turns : list place) :
      Prop :=
  Forall (in_woods trail_lengths) (spot :: turns) /\
  at_inter trail_starts trail_ends trail_lengths spot 1 /\
  at_inter trail_starts trail_ends trail_lengths (last turns
    spot) 1 /\
  legs_ok trail_starts trail_ends trail_lengths spot turns
    /\
  run_len spot turns = rN jog_distance.

(** Some leg of the run covers a stretch of trail [j]. *)
Fixpoint runs_on (j : N) (spot : place)
  (turns : list place) : Prop :=
  match turns with
  | [] => False
  | next_spot :: turns' =>
      (fst spot = j /\ fst next_spot = j /\ snd spot <> snd
        next_spot) \/
      runs_on j next_spot turns'
  end.

(** Trail [j] may be used by some jogger. *)
Definition used
  (trail_starts trail_ends trail_lengths : list N)
    (jog_distance j : N) : Prop :=
  exists spot turns,
    jog trail_starts trail_ends trail_lengths jog_distance
      spot turns /\
    runs_on j spot turns.

(** New lamps: distinct intersections. *)
Definition placement (intersection_count : N)
  (new_lamps : list N) : Prop :=
  NoDup new_lamps /\ Forall (inter intersection_count)
    new_lamps.

(** [intersection] has either an existing lamp or one of [new_lamps]. *)
Definition lit (lamps new_lamps : list N)
  (intersection : N) : Prop :=
  In intersection lamps \/ In intersection new_lamps.

(** Every trail a jogger may use has a lamp at one of its ends. *)
Definition safe (jog_distance : N)
    (trail_starts trail_ends trail_lengths lamps new_lamps :
      list N)
    : Prop :=
  forall j, j < len trail_starts ->
    used trail_starts trail_ends trail_lengths jog_distance
      j ->
    lit lamps new_lamps (get trail_starts j) \/
    lit lamps new_lamps (get trail_ends j).

(** [@inside joggers_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (intersection_count jog_distance : N)
    (trail_starts trail_ends trail_lengths lamps : list N) :
      Prop := {
  (* 2 <= N <= 5 * 10^4 (intersection_count) *)
  vi_n : 2 <= intersection_count <= 50000;
  (* 1 <= S <= 10^4 (jog_distance) *)
  vi_s : 1 <= jog_distance <= 10 ^ 4;
  (* then follow N - 1 lines with three integers a b d
     (trail_starts, trail_ends, trail_lengths) *)
  vi_trails : len trail_starts = intersection_count - 1 /\
              len trail_ends = len trail_starts /\
              len trail_lengths = len trail_starts;
  (* 1 <= a <= N, 1 <= b <= N *)
  vi_a : Forall (inter intersection_count) trail_starts;
  vi_b : Forall (inter intersection_count) trail_ends;
  (* 1 <= d <= 100 *)
  vi_d : Forall (fun trail_length => 1 <= trail_length <=
    100)
           trail_lengths;
  (* there is exactly one route between each pair of
     intersections *)
  vi_route : forall from_node to_node,
    inter intersection_count from_node ->
      inter intersection_count to_node ->
    exists trails, route trail_starts trail_ends from_node
      trails to_node;
  vi_route_unique : forall from_node to_node trails trails',
    route trail_starts trail_ends from_node trails to_node
      ->
    route trail_starts trail_ends from_node trails' to_node
      ->
    trails = trails';
  (* 0 <= L <= N *)
  vi_L : len lamps <= intersection_count;
  (* L distinct integers, lamps at intersections l_1 ..
     l_L (lamps) *)
  vi_l : Forall (inter intersection_count) lamps;
  vi_l_distinct : NoDup lamps;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the minimum number of additional lamps needed so every trail
    usable by a run of exactly [jog_distance] metres from the campus and back
    has a lamp at one of its ends. *)
Definition joggers_spec
  (intersection_count jog_distance : N)
    (trail_starts trail_ends trail_lengths lamps : list N)
    (output : N) : Prop :=
  (exists new_lamps, placement intersection_count new_lamps
    /\
     safe jog_distance trail_starts trail_ends trail_lengths
       lamps
       new_lamps /\
     len new_lamps = output) /\
  (forall new_lamps, placement intersection_count new_lamps
    ->
     safe jog_distance trail_starts trail_ends trail_lengths
       lamps
       new_lamps ->
     output <= len new_lamps).

(** ** Complexity *)

(** [@requirement] Runs in $O(V+E+L+1)$ steps, where $V$ is the intersection count, $E$ the trail count, and $L$ the number of lamps. *)
Definition joggers_time_spec (c1 c2 n_intersection_count n_trail_starts n_lamps steps : nat) : Prop :=
  (steps <= c1 * (n_intersection_count + n_trail_starts + n_lamps + 1) + c2)%nat.

(** ** Interface *)

(** Add the fewest lamps so every trail usable by an allowed jog has a lamp
    at one of its ends. Each jog starts and finishes at the campus, intersection
    1, and may turn around inside trails.
    - Input [intersection_count]: Number of intersections, numbered from one.
    - Input [jog_distance]: Exact length of each jog, in metres.
    - Input [trail_starts]: First intersection of each trail.
    - Input [trail_ends]: Second intersection of each trail.
    - Input [trail_lengths]: Length of each corresponding trail, in metres.
    - Input [lamps]: Intersection numbers with existing lamps.
    - Output [output]: Minimum number of additional lamps making every trail usable by such a jog lit at an endpoint. *)
Program joggers : uint -> uint -> array uint -> array uint
  ->
  array uint -> array uint -> uint.

(** [@example joggers]
    - Sample: 1
    - Input [intersection_count]: 5
    - Input [jog_distance]: 6
    - Input [trail_starts]: [1; 1; 4; 3]
    - Input [trail_ends]: [2; 3; 3; 5]
    - Input [trail_lengths]: [1; 1; 3; 2]
    - Input [lamps]: [1]
    - Output [output]: 1
*)

(** ** Bridge *)

(** [@requirement joggers_spec] [@fold full correctness statement] On
    valid represented inputs, [joggers] returns a represented output
    satisfying [joggers_spec]. *)
Specification joggers_correct :
  forall (intersection_count jog_distance : N)
         (trail_starts trail_ends trail_lengths lamps : list
           N)
         (intersection_count_int jog_distance_int : uint)
         (trail_starts_arr trail_ends_arr trail_lengths_arr
           lamps_arr
            : array uint),
  valid_input intersection_count jog_distance trail_starts
    trail_ends
    trail_lengths lamps ->
  repr intersection_count_int intersection_count ->
  repr jog_distance_int jog_distance ->
  repr trail_starts_arr trail_starts ->
    repr trail_ends_arr trail_ends ->
  repr trail_lengths_arr trail_lengths ->
    repr lamps_arr lamps ->
  exists output : N,
    repr (joggers intersection_count_int jog_distance_int
      trail_starts_arr
            trail_ends_arr trail_lengths_arr lamps_arr)
              output /\
    joggers_spec intersection_count jog_distance
      trail_starts trail_ends
      trail_lengths lamps output.

(** ** Complexity *)

(** [@hide] [joggers_cost] is the cost translation of [joggers] (the judge
    recomputes it and compares) ... *)
Complexity joggers_cost for joggers.

(** [@fold complexity bound] ... and runs in at most c1 * (n + t + l + 1) + c2 steps of the cost model on a valid input, n the number of intersections, t of trails and l of lamps (one traversal, then the tree dynamic programming), for two constants
    quantified before the inputs, on every valid input. [@requirement joggers_time_spec] *)
Specification joggers_time : exists c1 c2 : nat,
  forall (intersection_count jog_distance : N)
  (trail_starts trail_ends trail_lengths lamps : list
  N)
  (intersection_count_int jog_distance_int : uint)
  (trail_starts_arr trail_ends_arr trail_lengths_arr
  lamps_arr
  : array uint),
  valid_input intersection_count jog_distance trail_starts
  trail_ends
  trail_lengths lamps ->
  repr intersection_count_int intersection_count ->
  repr jog_distance_int jog_distance ->
  repr trail_starts_arr trail_starts ->
  repr trail_ends_arr trail_ends ->
  repr trail_lengths_arr trail_lengths ->
  repr lamps_arr lamps ->
  joggers_time_spec c1 c2 (size intersection_count_int) (size trail_starts_arr) (size lamps_arr) (cost6 joggers_cost intersection_count_int jog_distance_int trail_starts_arr trail_ends_arr trail_lengths_arr lamps_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
