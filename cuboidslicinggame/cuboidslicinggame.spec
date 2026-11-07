(** * Cuboid Slicing Game *)

(** ** Description *)

(** Determine the winner under optimal play in a game on integer-sized
    cuboids. Each move removes one unit-thick slice perpendicular to each
    axis from one cuboid, leaving up to eight smaller cuboids. The player
    making the last move wins.

    [@kattis cuboidslicinggame]
    - Difficulty: 4.2

    **Kattis Bounds**
    - 1 to 100 cuboids.
    - Each integer side length is from 1 to 30. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The two names of the input and of the output line; a
    type of the problem's own, the same on both sides. *)
Inductive player := Ruben | Albert.

(** [@hide] Machine and mathematical player values are
    identical. *)
Instance repr_player : Repr player player :=
  fun machine_player math_player => machine_player =
    math_player.

(** The other player. *)
Definition opponent (who : player) : player :=
  match who with Ruben => Albert | Albert => Ruben end.

(* Math side. *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** A cuboid x * y * z, and a position of the game: the
    cuboids on the table. *)
Definition cuboid : Type := (N * N * N)%type.
(** The cuboids remaining in the game. *)
Definition position : Type := list cuboid.

(** Cutting a side of length side at plane cut (1 <= cut
    <= side) leaves cut-1 and side-cut. *)
Definition sides (side cut : N) : list N :=
  [cut - 1; side - cut].

(** The up to 8 cuboids left when x_side * y_side *
    z_side is cut at planes x_cut, y_cut and z_cut:
    every combination of the remaining sides, those with
    a side 0 dropped. *)
Definition pieces
  (x_side y_side z_side x_cut y_cut z_cut : N) : position :=
  filter (fun '(x_rest, y_rest, z_rest) =>
            ((0 <? x_rest) && (0 <? y_rest) &&
              (0 <? z_rest))%bool)
    (flat_map (fun x_rest => flat_map (fun y_rest =>
       map (fun z_rest => (x_rest, y_rest, z_rest))
       (sides z_side z_cut)) (sides y_side y_cut))
         (sides x_side x_cut)).

(** A legal move: choose a cuboid and three planes on
    it, and replace the cuboid by its pieces. *)
Inductive move : position -> position -> Prop :=
  | move_cut :
    forall before after x_side y_side z_side x_cut y_cut
    z_cut,
      1 <= x_cut <= x_side -> 1 <= y_cut <= y_side
        -> 1 <= z_cut <= z_side ->
      move (before ++ (x_side, y_side, z_side) :: after)
           (before ++ pieces x_side y_side z_side x_cut
             y_cut z_cut ++ after).

(** Optimal play: the player to move wins iff some move
    leads to a position lost for the player to move
    then; it loses iff every move leads to a won
    position (so the empty position, where the opponent
    removed the last cuboid, is lost). *)
Inductive wins : position -> Prop :=
  | wins_move : forall state next_state,
      move state next_state -> loses next_state
        -> wins state
with loses : position -> Prop :=
  | loses_all : forall state,
      (forall next_state, move state next_state
        -> wins next_state) ->
      loses state.

(** The starting position: cuboid i is x_lengths_i *
    y_lengths_i * z_lengths_i, in input order. *)
Definition initial
  (x_lengths y_lengths z_lengths : list N) : position :=
  combine (combine x_lengths y_lengths) z_lengths.

(** [@inside winner_correct] The statement's bounds; the
    N input lines are the three parallel lists of the
    coordinates x, y, z. *)
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

(** [@requirement] [@short must return the winner under
    optimal play.] The answer is first_player when the
    player to move wins the starting position, its
    opponent when the player to move loses it. *)
Definition winner_spec (first_player : player)
    (x_lengths y_lengths z_lengths : list N)
      (output : player)
    : Prop :=
  (output = first_player <->
     wins (initial x_lengths y_lengths z_lengths)) /\
  (output = opponent first_player <->
     loses (initial x_lengths y_lengths z_lengths)).

(** ** Interface *)

(** The machine-level interface.
    - Input [first_player]:
    - Input [x_lengths]:
    - Input [y_lengths]:
    - Input [z_lengths]:
    - Output [output]: *)
Program winner : player -> array uint -> array uint
  -> array uint -> player.

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

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
