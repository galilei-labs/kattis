(** * Maze Movement *)

(** ** Description *)

(** A maze has rooms with distinct integer room numbers. Two rooms have a
    passage when their numbers have greatest common divisor greater than one;
    that divisor is the passage capacity in each direction, in people per
    minute. Find the maximum rate of movement from the lowest-numbered room
    (the entrance) to the highest-numbered room (the exit).

    [@kattis mazemovement]
    - Difficulty: 2.8
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Distinct room count: $2 \le n \le 10^{3}$; room numbers: $2 \le a_i \le 2 \times 10^{9}$.
    - The maximum flow is at most $10^{9}$. *)

(** ** Examples *)

(** - Input convention: Room count, followed by distinct room numbers, one per line.
    - Output convention: The maximum number of people per minute that can move from the entrance to the exit. *)
(* Input:
4
4
6
8
9
Output:
3
*)

(** ** [@hide] Environment *)
(* @function        mazemovement
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         The rooms of a maze are given by their distinct numbers;
                    two rooms whose numbers have a common factor greater than
                    one are joined by a passage on which gcd(x, y) people per
                    minute can walk in each direction, simultaneously.
                    [mazemovement rooms] is the maximum number of people per
                    minute that can enter at the lowest-numbered room and
                    leave at the highest-numbered one, nobody waiting in a
                    room.
                    It runs in at most c1 * (n + 1)^4 + c2 steps of the cost
                    model on a valid input, n the number of rooms: the
                    generic push-relabel bound on the dense n x n network
                    (at most n^2 relabels, n^3 saturating pushes and n^4
                    non-saturating ones by the potential of the active
                    heights), the gap and global relabelings within it, the
                    gcd table in n^2 word gcds; the n^3 of the FIFO
                    selection is not stated, for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The room number at zero-based position [i] in [rooms]. A room's position
    identifies it in the flow model; its number determines passage capacities. *)
Definition room (rooms : list N) (i : N) : N :=
  nth (N.to_nat i) rooms 0.

(** The sum of [term] over zero-based indices below [count]. *)
Fixpoint sum_below (term : N -> N) (count : nat) : N :=
  match count with
  | O => 0
  | S below => sum_below term below + term (N.of_nat below)
  end.

(** The entrance is the position of the lowest-numbered room. *)
Definition entrance (rooms : list N)
  (entry_position : N) : Prop :=
  entry_position < len rooms /\
  forall j, j < len rooms ->
    room rooms entry_position <= room rooms j.

(** The exit is the position of the highest-numbered room. *)
Definition exit (rooms : list N)
  (exit_position : N) : Prop :=
  exit_position < len rooms /\
  forall j, j < len rooms ->
    room rooms j <= room rooms exit_position.

(** The directed passage capacity between rooms [i] and [j], in people per minute:
    their greatest common divisor when it exceeds one. Self-passages and coprime
    pairs have capacity zero. *)
Definition cap (rooms : list N) (i j : N) : N :=
  let common := N.gcd (room rooms i) (room rooms j) in
  if N.eqb i j then 0 else if 1 <? common then common else
    0.

(** The total number of people leaving [position] per minute under [pattern]. *)
Definition outflow (rooms : list N)
  (pattern : N -> N -> N) (position : N)
    : N :=
  sum_below (fun j => pattern position j) (List.length
    rooms).
(** The total number of people arriving at [position] per minute under [pattern]. *)
Definition inflow (rooms : list N)
  (pattern : N -> N -> N) (position : N)
    : N :=
  sum_below (fun j => pattern j position) (List.length
    rooms).

(** A walking pattern from [entry_position] to [exit_position]: every
    passage is used within its limit in each direction, and nobody
    waits in a room other than [entry_position] and [exit_position]. *)
Definition is_walk (rooms : list N)
  (entry_position exit_position : N)
    (pattern : N -> N -> N) : Prop :=
  (forall i j, i < len rooms -> j < len rooms ->
     pattern i j <= cap rooms i j) /\
  (forall position, position < len rooms ->
     position <> entry_position ->
       position <> exit_position ->
     outflow rooms pattern position = inflow rooms pattern
       position).

(** The number of people per minute entering the maze at
    [entry_position]. *)
Definition entering (rooms : list N) (entry_position : N)
    (pattern : N -> N -> N) : Z :=
  (Z.of_N (outflow rooms pattern entry_position)
   - Z.of_N (inflow rooms pattern entry_position))%Z.

(** [@inside mazemovement_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (rooms : list N) : Prop := {
  (* an integer 2 <= n <= 10^3 indicating the number of
     rooms *)
  vi_n : 2 <= len rooms <= 1000;
  (* each room number x satisfies 2 <= x <= 2 * 10^9 *)
  vi_range : Forall (fun number => 2 <= number <= 2 * 10 ^
    9) rooms;
  (* n unique integers *)
  vi_unique : NoDup rooms;
  (* no maze supports more than 10^9 people entering per
     minute *)
  vi_answer : forall entry_position exit_position pattern,
    entrance rooms entry_position ->
      exit rooms exit_position ->
    is_walk rooms entry_position exit_position pattern ->
    (entering rooms entry_position pattern <= 10 ^ 9)%Z;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the maximum flow, in people per minute, from the
    lowest-numbered room to the highest-numbered room, using the specified
    GCD-based passage capacities. *)
Definition mazemovement_spec (rooms : list N)
  (output : N) : Prop :=
  forall entry_position exit_position,
    entrance rooms entry_position ->
      exit rooms exit_position ->
    (exists pattern, is_walk rooms entry_position
      exit_position pattern /\
       entering rooms entry_position pattern = Z.of_N
         output) /\
    (forall pattern, is_walk rooms entry_position
      exit_position pattern ->
       (entering rooms entry_position pattern <= Z.of_N
         output)%Z).

(** ** Complexity *)

(** [@requirement] Runs in $O(n^4)$ steps, where $n$ is the number of rooms. *)
Definition mazemovement_time_spec (c1 c2 n_rooms steps : nat) : Prop :=
  (steps <= c1 * ((n_rooms + 1) * (n_rooms + 1) * (n_rooms + 1) * (n_rooms + 1)) + c2)%nat.

(** ** Interface *)

(** Find the maximum rate of movement through the maze from the lowest-numbered
    room to the highest-numbered room. Passage capacities are the GCDs of room
    numbers, with no passage for coprime numbers.
    - Input [rooms]: Distinct room numbers defining the passage capacities.
    - Output [output]: Maximum flow from entrance to exit, in people per minute. *)
Program mazemovement : array uint -> uint.

(** [@example mazemovement]
    - Sample: 1
    - Input [rooms]: [4; 6; 8; 9]
    - Output [output]: 3
*)

(** ** Bridge *)

(** [@requirement mazemovement_spec] [@fold full correctness statement]
    On valid represented inputs, [mazemovement] returns a
    represented output satisfying [mazemovement_spec]. *)
Specification mazemovement_correct :
  forall (rooms : list N) (rooms_arr : array uint),
  valid_input rooms -> repr rooms_arr rooms ->
  exists output : N,
    repr (mazemovement rooms_arr) output /\
    mazemovement_spec rooms output.

(** ** Complexity *)

(** [@hide] [mazemovement_cost] is the cost translation of [mazemovement] (the judge
    recomputes it and compares) ... *)
Complexity mazemovement_cost for mazemovement.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1)^4 + c2 steps of the cost model on a valid input, n the number of rooms: the generic push-relabel bound on the dense n x n network (at most n^2 relabels, n^3 saturating pushes and n^4 non-saturating ones by the potential of the active heights), the gap and global relabelings within it, the gcd table in n^2 word gcds; the n^3 of the FIFO selection is not stated, for two constants
    quantified before the inputs, on every valid input. [@requirement mazemovement_time_spec] *)
Specification mazemovement_time : exists c1 c2 : nat,
  forall (rooms : list N) (rooms_arr : array uint),
  valid_input rooms -> repr rooms_arr rooms ->
  mazemovement_time_spec c1 c2 (size rooms_arr) (cost1 mazemovement_cost rooms_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
