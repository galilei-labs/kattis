(** * Security Badge *)

(** ** Description *)

(** Each edge of a directed graph permits an inclusive interval of integer
    labels. Count the labels that permit a path from a specified source to a
    destination.

    [@kattis securitybadge]
    - Difficulty: 7.0
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 2 to 1000 vertices; 1 to 5000 directed edges.
    - Labels from 1 to B, where B <= 1000000000.
    - Source and destination differ; each ordered vertex pair has at most
      one edge, with an allowed interval inside 1 through B. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Relations.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* The locks are the L input lines [a b x y], as four
   parallel lists: lock_sources (from), lock_targets
   (to), lowest_badges (lowest badge), highest_badges
   (highest badge). *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The i-th element of l, 0-based. *)
Definition get (l : list N) (i : N) : N :=
  nth (N.to_nat i) l 0.

(** Badge badge passes from room room to room room'
    through a single lock. *)
Definition step
    (lock_sources lock_targets lowest_badges highest_badges
      : list N)
    (badge room room' : N) : Prop :=
  exists i, i < len lock_sources /\ get lock_sources i =
    room /\
            get lock_targets i = room' /\
            get lowest_badges i <= badge <= get
            highest_badges i.

(** Badge badge gets from room room to room room': zero
    or more steps. *)
Definition walks
    (lock_sources lock_targets lowest_badges highest_badges
      : list N)
    (badge room room' : N) : Prop :=
  clos_refl_trans N
    (step lock_sources lock_targets lowest_badges
      highest_badges badge)
    room room'.

(** Badge badge is in 1 .. [badge_count] and gets from
    [start] to [destination]. *)
Definition good (badge_count start destination : N)
    (lock_sources lock_targets lowest_badges highest_badges
      : list N )
    (badge : N) : Prop :=
  1 <= badge <= badge_count /\
  walks lock_sources lock_targets lowest_badges
    highest_badges badge
    start destination.

(** [@inside securitybadge_correct] Valid input. *)
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
  (* 2 <= N <= 1 000 *)
  vi_n : 2 <= room_count <= 1000;
  (* 1 <= L <= 5 000 *)
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

(** [@requirement] [@short Count the badge numbers that
    allow a route from the starting room to the
    destination through directed, badge-restricted
    doors.] The answer is the number of [good] badges:
    [output] is the length of a duplicate-free list
    holding exactly the [good] badges. *)
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

(** ** Interface *)

(** Count the badge numbers that allow a route from the
    starting room to the [destination] through directed,
    badge-restricted doors.
    - Input [room_count]:
    - Input [badge_count]:
    - Input [start]:
    - Input [destination]:
    - Input [lock_sources]:
    - Input [lock_targets]:
    - Input [lowest_badges]:
    - Input [highest_badges]:
    - Output [output]: *)
Program securitybadge : uint -> uint -> uint -> uint ->
  array uint ->
  array uint -> array uint -> array uint -> uint.

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

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
