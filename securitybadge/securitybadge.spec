(** * Security Badge *)

(** ** Description *)

(** Rooms in an office are connected by electronic door locks. Each lock
    permits passage in one direction only and accepts badges whose ID numbers
    lie between its lower and upper bounds, inclusive. Permission to pass in
    the reverse direction is separate.

    Count the badge numbers from one through the given badge count that let
    a person travel from the starting room to the destination. The person
    must use the same badge at every lock along the route.

    [@kattis securitybadge]
    - Difficulty: 7.0
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 10^{3}$; Directed edge count: $1 \le m \le 5 \times 10^{3}$.
    - Labels: $1 \le b \le B \le 10^{9}$.
    - Source and destination differ; each ordered vertex pair has at most
      one edge, with an allowed interval whose endpoints satisfy $1 \le l \le r \le B$. *)

(** ** Examples *)

(** - Input convention: Vertex, edge and label counts; source and destination; then edges with inclusive label ranges.
    - Output convention: The count of labels permitting a source-to-destination path. *)
(* Input:
4 5 10
3 2
1 2 4 7
3 1 1 6
3 4 7 10
2 4 3 5
4 2 8 9
Output:
5
*)

(** ** [@hide] Environment *)

(* @function        securitybadge
   @signature       uint -> uint -> uint -> uint -> array uint ->
                    array uint -> array uint -> array uint -> uint
   @math_signature  N -> N -> N -> N -> list N -> list N -> list N ->
                    list N -> N
   @summary         [securitybadge room_count badge_count start
                    destination lock_sources lock_targets lowest_badges
                    highest_badges] counts the badge numbers badge in
                    1 .. badge_count that can get from room start to room
                    destination, the rooms being 1 .. room_count and lock
                    i a one-way door from room lock_sources_i to room
                    lock_targets_i that lets through the badges
                    lowest_badges_i .. highest_badges_i (inclusive).  A
                    badge gets from start to destination when some
                    sequence of locks it passes leads from start to
                    destination.
                    It runs in at most c1 * (L + 1) * (n + L + log2 L + 1) +
                    c2 steps of the cost model on a valid input, n the
                    number of rooms and L of locks (the sort of the interval
                    bounds, then one reachability search per elementary
                    interval), for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Relations.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* The locks are the L input lines [a b x y], as four
   parallel lists: lock_sources (from), lock_targets
   (to), lowest_badges (lowest badge), highest_badges
   (highest badge). *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [i] in [l], or zero beyond the end. *)
Definition get (l : list N) (i : N) : N :=
  nth (N.to_nat i) l 0.

(** A directed lock from [room] to [room'] permits [badge]. *)
Definition step
    (lock_sources lock_targets lowest_badges highest_badges
      : list N)
    (badge room room' : N) : Prop :=
  exists i, i < len lock_sources /\ get lock_sources i =
    room /\
            get lock_targets i = room' /\
            get lowest_badges i <= badge <= get
            highest_badges i.

(** [badge] permits a walk of zero or more locks from [room] to [room']. *)
Definition walks
    (lock_sources lock_targets lowest_badges highest_badges
      : list N)
    (badge room room' : N) : Prop :=
  clos_refl_trans N
    (step lock_sources lock_targets lowest_badges
      highest_badges badge)
    room room'.

(** [badge] is in the allowed range from one through [badge_count] and permits a
    walk from [start] to [destination]. *)
Definition good (badge_count start destination : N)
    (lock_sources lock_targets lowest_badges highest_badges
      : list N )
    (badge : N) : Prop :=
  1 <= badge <= badge_count /\
  walks lock_sources lock_targets lowest_badges
    highest_badges badge
    start destination.

(** [@inside securitybadge_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (room_count badge_count start destination
  : N)
    (lock_sources lock_targets lowest_badges highest_badges
      : list N )
    : Prop := {
  (* L lines, each describing a lock as four integers a b
     x y *)
  vi_lb_len : len lock_targets = len lock_sources;
  vi_lx_len : len lowest_badges = len lock_sources;
  vi_ly_len : len highest_badges = len lock_sources;
  (* 2 <= N <= 10^3 *)
  vi_n : 2 <= room_count <= 1000;
  (* 1 <= L <= 5 * 10^3 *)
  vi_l : 1 <= len lock_sources <= 5000;
  (* 1 <= B <= 10^9 *)
  vi_b : 1 <= badge_count <= 10 ^ 9;
  (* 1 <= S <= N, 1 <= D <= N, S <> D *)
  vi_s : 1 <= start <= room_count;
  vi_d : 1 <= destination <= room_count;
  vi_sd : start <> destination;
  (* 1 <= a, b <= N, a <> b, 1 <= x <= B, 1 <= y <= B, x
     <= y *)
  vi_lock : forall i, i < len lock_sources ->
    1 <= get lock_sources i <= room_count /\
    1 <= get lock_targets i <= room_count /\
    get lock_sources i <> get lock_targets i /\
    1 <= get lowest_badges i <= badge_count /\
    1 <= get highest_badges i <= badge_count /\
    get lowest_badges i <= get highest_badges i;
  (* no (a, b) pair will occur more than once *)
  vi_pairs : forall i j, i < len lock_sources -> j < len
    lock_sources ->
    get lock_sources i = get lock_sources j ->
    get lock_targets i = get lock_targets j -> i = j;
}.

(** ** Correctness *)

(** [@requirement]
    The output counts badge IDs from one through [badge_count] that permit
    travel from the starting room to the destination, using the same badge
    at every directed lock along the route. *)
Definition securitybadge_spec
  (room_count badge_count start destination : N)
  (lock_sources lock_targets lowest_badges highest_badges :
    list N )
  (output : N)
  : Prop :=
  exists badges : list N,
    NoDup badges /\
    (forall badge, In badge badges <->
       good badge_count start destination
         lock_sources lock_targets lowest_badges
           highest_badges badge) /\
    output = len badges.

(** ** Complexity *)

(** [@requirement] Runs in $O((E+1)(V+E+\log(E+2)))$ steps, where $V$ is the room count and $E$ the number of locks. *)
Definition securitybadge_time_spec (c1 c2 n_lock_sources n_room_count steps : nat) : Prop :=
  (steps <= c1 * ((n_lock_sources + 1) * (n_room_count + n_lock_sources + Nat.log2 (n_lock_sources) + 1)) + c2)%nat.

(** ** Interface *)

(** Count the badge IDs that permit travel from the starting room to the
    destination using the same badge at every directed lock along the route.
    - Input [room_count]: Number of rooms.
    - Input [badge_count]: Largest badge ID; IDs start at one.
    - Input [start]: Starting room.
    - Input [destination]: Room to reach.
    - Input [lock_sources]: Room each directed lock leads from.
    - Input [lock_targets]: Room each corresponding lock leads to.
    - Input [lowest_badges]: Smallest badge ID accepted by each lock, inclusive.
    - Input [highest_badges]: Largest badge ID accepted by each lock, inclusive.
    - Output [output]: Number of badge IDs for which such a route exists. *)
Program securitybadge : uint -> uint -> uint -> uint ->
  array uint ->
  array uint -> array uint -> array uint -> uint.

(** [@example securitybadge]
    - Sample: 1
    - Input [room_count]: 4
    - Input [badge_count]: 10
    - Input [start]: 3
    - Input [destination]: 2
    - Input [lock_sources]: [1; 3; 3; 2; 4]
    - Input [lock_targets]: [2; 1; 4; 4; 2]
    - Input [lowest_badges]: [4; 1; 7; 3; 8]
    - Input [highest_badges]: [7; 6; 10; 5; 9]
    - Output [output]: 5
*)

(** ** Bridge *)

(** [@requirement securitybadge_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [securitybadge_spec]. *)
Specification securitybadge_correct :
  forall (room_count badge_count start destination : N)
         (lock_sources lock_targets lowest_badges
           highest_badges : list N )
         (room_count_int badge_count_int start_int
           destination_int : uint)
         (lock_sources_arr lock_targets_arr : array uint)
         (lowest_badges_arr highest_badges_arr : array uint
           ),
  valid_input room_count badge_count start destination
    lock_sources lock_targets lowest_badges highest_badges
      ->
  repr room_count_int room_count -> repr badge_count_int
    badge_count ->
  repr start_int start -> repr destination_int destination
    ->
  repr lock_sources_arr lock_sources -> repr
    lock_targets_arr lock_targets ->
  repr lowest_badges_arr lowest_badges ->
  repr highest_badges_arr highest_badges ->
  exists output : N,
    repr (securitybadge room_count_int badge_count_int
      start_int
            destination_int lock_sources_arr
            lock_targets_arr
            lowest_badges_arr highest_badges_arr) output /\
    securitybadge_spec room_count badge_count start
      destination
      lock_sources lock_targets lowest_badges highest_badges
        output.

(** ** Complexity *)

(** [@hide] [securitybadge_cost] is the cost translation of [securitybadge] (the judge
    recomputes it and compares) ... *)
Complexity securitybadge_cost for securitybadge.

(** [@fold complexity bound] ... and runs in at most c1 * (L + 1) * (n + L + log2 L + 1) + c2 steps of the cost model on a valid input, n the number of rooms and L of locks (the sort of the interval bounds, then one reachability search per elementary interval), for two constants
    quantified before the inputs, on every valid input. [@requirement securitybadge_time_spec] *)
Specification securitybadge_time : exists c1 c2 : nat,
  forall (room_count badge_count start destination : N)
  (lock_sources lock_targets lowest_badges
  highest_badges : list N )
  (room_count_int badge_count_int start_int
  destination_int : uint)
  (lock_sources_arr lock_targets_arr : array uint)
  (lowest_badges_arr highest_badges_arr : array uint
  ),
  valid_input room_count badge_count start destination
  lock_sources lock_targets lowest_badges highest_badges
  ->
  repr room_count_int room_count -> repr badge_count_int
  badge_count ->
  repr start_int start -> repr destination_int destination
  ->
  repr lock_sources_arr lock_sources -> repr
  lock_targets_arr lock_targets ->
  repr lowest_badges_arr lowest_badges ->
  repr highest_badges_arr highest_badges ->
  securitybadge_time_spec c1 c2 (size lock_sources_arr) (size room_count_int) (cost8 securitybadge_cost room_count_int badge_count_int start_int destination_int lock_sources_arr lock_targets_arr lowest_badges_arr highest_badges_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
