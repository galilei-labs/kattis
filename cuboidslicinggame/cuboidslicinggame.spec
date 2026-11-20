(** * Cuboid Slicing Game *)

(** ** Description *)

(** Determine the winner under optimal play in a game on integer-sized
    cuboids. Each move removes one unit-thick slice perpendicular to each
    axis from one cuboid, leaving up to eight smaller cuboids. The player
    making the last move wins.

    [@kattis cuboidslicinggame]
    - Difficulty: 4.2
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Cuboid count: $1 \le n \le 100$.
    - Each integer side length satisfies $1 \le s \le 30$. *)

(** ** Examples *)

(** - Input convention: Starting player, cuboid count, then three integer dimensions per cuboid.
    - Output convention: RUBEN or ALBERT, identifying the winning player under optimal play. *)
(* Input:
RUBEN
1
4 1 7
Output:
RUBEN
*)

(** ** [@hide] Environment *)

(* @function        winner
   @signature       player -> array uint -> array uint -> array uint -> player
   @math_signature  player -> list N -> list N -> list N -> player
   @summary         [winner first_player x_lengths y_lengths z_lengths] is
                    the player who wins the Cuboid Slicing Game when
                    [first_player] moves first from the cuboids
                    x_lengths_i x y_lengths_i x z_lengths_i and both play
                    optimally. A move cuts one cuboid along three planes
                    through it, leaving up to 8 smaller cuboids; the player
                    who removes the last cuboid wins.
                    It runs in at most c1 * ((M + 1)^6 + N) + c2 steps of
                    the cost model on a valid input, M the largest side
                    ([max_size] over the three columns) and N the number of
                    cuboids (the Grundy table over the canonical cuboids up
                    to M, M^3 of them with at most M^3 cuts each, then one
                    fold over the input), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The two players, using the same player type in machine and mathematical results. *)
Inductive player := Ruben | Albert.

(** [@hide] Machine and mathematical player values are
    identical. *)
Instance repr_player : Repr player player :=
  fun machine_player math_player => machine_player =
    math_player.

(** [@hide] The cost translation of [player] and the witness of a machine
    player (the vocabulary of [KattisLib.Cost]), for the bound below. *)
Elpi complexity player.
Instance witness_player : Witness player (fun CM p => player_cost CM p) :=
  fun p => match p with
           | Ruben => Ruben_cost stepsCM
           | Albert => Albert_cost stepsCM
           end.

(** The other player. *)
Definition opponent (who : player) : player :=
  match who with Ruben => Albert | Albert => Ruben end.

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The three side lengths of a cuboid. *)
Definition cuboid : Type := (N * N * N)%type.
(** The cuboids remaining in the game. *)
Definition position : Type := list cuboid.

(** Cutting a side of length [side] at plane [cut] leaves lengths [cut - 1] and
    [side - cut]. *)
Definition sides (side cut : N) : list N :=
  [cut - 1; side - cut].

(** The cuboids remaining after cuts at [x_cut], [y_cut], and [z_cut] along
    the three sides. All combinations of the remaining side lengths are included;
    pieces with a zero side length are discarded. *)
Definition pieces
  (x_side y_side z_side x_cut y_cut z_cut : N) : position :=
  filter (fun '(x_rest, y_rest, z_rest) =>
            ((0 <? x_rest) && (0 <? y_rest) &&
              (0 <? z_rest))%bool)
    (flat_map (fun x_rest => flat_map (fun y_rest =>
       map (fun z_rest => (x_rest, y_rest, z_rest))
       (sides z_side z_cut)) (sides y_side y_cut))
         (sides x_side x_cut)).

(** [move position_before position_after] means that a legal move transforms
    [position_before] into [position_after]: choose a cuboid and three cutting
    planes, and replace that cuboid by its pieces. *)
Inductive move : position -> position -> Prop :=
  | move_cut :
    forall before after x_side y_side z_side x_cut y_cut
    z_cut,
      1 <= x_cut <= x_side -> 1 <= y_cut <= y_side
        -> 1 <= z_cut <= z_side ->
      move (before ++ (x_side, y_side, z_side) :: after)
           (before ++ pieces x_side y_side z_side x_cut
             y_cut z_cut ++ after).

(** [wins state] means that the player to move in [state] has a winning strategy;
    [loses state] means that every legal move leaves the next player a winning
    position. A position is winning exactly when some legal move leaves a losing
    position. A position with no legal move is losing. *)
Inductive wins : position -> Prop :=
  | wins_move : forall state next_state,
      move state next_state -> loses next_state
        -> wins state
with loses : position -> Prop :=
  | loses_all : forall state,
      (forall next_state, move state next_state
        -> wins next_state) ->
      loses state.

(** The starting cuboids, with side lengths taken from the corresponding entries of
    [x_lengths], [y_lengths], and [z_lengths]. *)
Definition initial
  (x_lengths y_lengths z_lengths : list N) : position :=
  combine (combine x_lengths y_lengths) z_lengths.

(** [@inside winner_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (x_lengths y_lengths z_lengths : list N) : Prop := {
  (* 1 <= N <= 100 *)
  vi_n : 1 <= len x_lengths <= 100;
  (* each of the N lines holds the three numbers x, y and z
    *)
  vi_ys_len : len y_lengths = len x_lengths;
  vi_zs_len : len z_lengths = len x_lengths;
  (* 1 <= x, y, z <= 30 *)
  vi_xs : Forall
    (fun x_length => 1 <= x_length <= 30) x_lengths;
  vi_ys : Forall
    (fun y_length => 1 <= y_length <= 30) y_lengths;
  vi_zs : Forall
    (fun z_length => 1 <= z_length <= 30) z_lengths;
}.

(** ** Correctness *)

(** [@requirement]
    The output identifies the winner under optimal play from the initial cuboid
    configuration and starting player. *)
Definition winner_spec (first_player : player)
    (x_lengths y_lengths z_lengths : list N)
      (output : player)
    : Prop :=
  (output = first_player <->
     wins (initial x_lengths y_lengths z_lengths)) /\
  (output = opponent first_player <->
     loses (initial x_lengths y_lengths z_lengths)).

(** ** Complexity *)

(** [@requirement] Runs in $O((X+Y+Z+1)^6+n)$ steps, where $X$, $Y$, and $Z$ are the maximum side lengths in each dimension and $n$ is the number of cuboids. *)
Definition winner_time_spec (c1 c2 max_x_lengths max_y_lengths max_z_lengths n_x_lengths steps : nat) : Prop :=
  (steps <= c1 * ((max_x_lengths + max_y_lengths + max_z_lengths + 1) ^ 6 + n_x_lengths) + c2)%nat.

(** ** Interface *)

(** Determine the winner under optimal play in a game on integer-sized cuboids. Each move
    removes one unit-thick slice perpendicular to each axis from one cuboid, leaving up
    to eight smaller cuboids. The player making the last move wins.
    - Input [first_player]: Player making the first move.
    - Input [x_lengths]: First side length of each cuboid.
    - Input [y_lengths]: Second side length of each cuboid.
    - Input [z_lengths]: Third side length of each cuboid.
    - Output [output]: The output identifies the winner under optimal play from the initial cuboid configuration and starting player. *)
Program winner : player -> array uint -> array uint
  -> array uint -> player.

(** [@example winner]
    - Sample: 1
    - Input [first_player]: Ruben
    - Input [x_lengths]: [4]
    - Input [y_lengths]: [1]
    - Input [z_lengths]: [7]
    - Output [output]: Ruben
*)

(** ** Bridge *)

(** [@requirement winner_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [winner_spec]. *)
Specification winner_correct :
  forall (first_player : player)
    (x_lengths y_lengths z_lengths : list N)
         (first_player_arg : player)
         (x_lengths_arr y_lengths_arr z_lengths_arr : array
           uint),
  valid_input x_lengths y_lengths z_lengths ->
  repr first_player_arg first_player ->
  repr x_lengths_arr x_lengths
    -> repr y_lengths_arr y_lengths ->
  repr z_lengths_arr z_lengths ->
  exists output : player,
    repr (winner first_player_arg x_lengths_arr
      y_lengths_arr z_lengths_arr)
      output /\
    winner_spec first_player x_lengths y_lengths z_lengths
      output.

(** ** Complexity *)

(** [@hide] [winner_cost] is the cost translation of [winner] (the judge
    recomputes it and compares) ... *)
Complexity winner_cost for winner.

(** [@fold complexity bound] ... and runs in at most c1 * ((M + 1)^6 + N) + c2 steps of the cost model on a valid input, M the largest side ([max_size] over the three columns) and N the number of cuboids (the Grundy table over the canonical cuboids up to M, M^3 of them with at most M^3 cuts each, then one fold over the input), for two constants
    quantified before the inputs, on every valid input. [@requirement winner_time_spec] *)
Specification winner_time : exists c1 c2 : nat,
  forall (first_player : player)
  (x_lengths y_lengths z_lengths : list N)
  (first_player_arg : player)
  (x_lengths_arr y_lengths_arr z_lengths_arr : array
  uint),
  valid_input x_lengths y_lengths z_lengths ->
  repr first_player_arg first_player ->
  repr x_lengths_arr x_lengths
  -> repr y_lengths_arr y_lengths ->
  repr z_lengths_arr z_lengths ->
  winner_time_spec c1 c2 (max_size x_lengths_arr) (max_size y_lengths_arr) (max_size z_lengths_arr) (size x_lengths_arr) (cost4 winner_cost first_player_arg x_lengths_arr y_lengths_arr z_lengths_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
