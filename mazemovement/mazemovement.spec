(** * Maze Movement *)

(** ** Description *)

(** Build a network on distinct integer labels, joining two vertices when
    their greatest common divisor exceeds one and using that divisor as
    capacity in each direction. Find the maximum flow from the smallest
    label to the largest.

    [@kattis mazemovement]
    - Difficulty: 2.8
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $2\text{ to }1{,}000$ distinct labels, each in $[2, 2{,}000{,}000{,}000]$.
    - The maximum flow is at most $10^{9}$. *)

(** ** Examples *)

(** - Input convention: Vertex count, followed by distinct integer labels, one per line.
    - Output convention: The maximum flow from the smallest label to the largest. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. A room is designated by its position in the list (the
    room numbers are distinct); a walking pattern [pattern] gives,
    for every ordered pair of positions (i, j), the number of people
    per minute walking from room i to room j. The number of elements
    of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of the room at position i. *)
Definition room (rooms : list N) (i : N) : N :=
  nth (N.to_nat i) rooms 0.

(** term 0 + term 1 + ... + term (count - 1). *)
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

(** The number of people per minute that can walk from room i to room j:
    their largest common factor if it is greater than one, and no
    passage (0) otherwise, or from a room to itself. *)
Definition cap (rooms : list N) (i j : N) : N :=
  let common := N.gcd (room rooms i) (room rooms j) in
  if N.eqb i j then 0 else if 1 <? common then common else
    0.

(** People leaving room [position] per minute, and people arriving in
    it. *)
Definition outflow (rooms : list N)
  (pattern : N -> N -> N) (position : N)
    : N :=
  sum_below (fun j => pattern position j) (List.length
    rooms).
(** The [inflow] definition. *)
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
  (* an integer 2 <= n <= 1000 indicating the number of
     rooms *)
  vi_n : 2 <= len rooms <= 1000;
  (* each room number is in the range [2, 2 * 10^9] *)
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
    The output is the maximum flow from the smallest to the largest vertex label, using
    the specified GCD-based edge capacities. *)
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

(** ** Interface *)

(** Build a network on distinct integer labels, joining two vertices when their greatest
    common divisor exceeds one and using that divisor as capacity in each direction.
    Find the maximum flow from the smallest label to the largest.
    - Input [rooms]: Distinct vertex labels defining the GCD-based capacities.
    - Output [output]: The output is the maximum flow from the smallest to the largest vertex label, using the specified GCD-based edge capacities. *)
Program mazemovement : array uint -> uint.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
