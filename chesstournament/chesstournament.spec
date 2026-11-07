(** * Chess Tournament *)

(** ** Description *)

(** Decide whether reported wins and draws admit consistent numerical skill
    levels: a win requires a strictly higher level, and a draw requires
    equal levels.

    [@kattis chesstournament]
    - Difficulty: 5.0

    **Kattis Bounds**
    - 2 to 50000 players; 1 to 250000 reported matches.
    - At most one match per pair; every player appears in at least one
      match. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
3 3
0 > 1
1 = 2
0 = 2
Output:
inconsistent
*)

(** ** [@hide] Environment *)

(* @function        chess_consistent
   @signature       uint -> array uint -> array bool -> array uint -> bool
   @math_signature  N -> list N -> list bool -> list N -> bool
   @summary         [chess_consistent player_count first_players wins
                    second_players] reads m reported matches between players
                    0..player_count-1, match j being "first_players_j beat
                    second_players_j" when wins_j is true and
                    "first_players_j drew with second_players_j" when it is
                    false.  It returns true ("consistent") exactly when some
                    skill level per player explains every match, the more
                    skilled player always winning and a draw happening iff
                    the two skills are equal; false ("inconsistent")
                    otherwise.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The m match lines "K s L" are three parallel
  lists, one per
   column; the symbol s is a bool: true for '>', false for
     '='. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The j-th element of l (default beyond the end). *)
Definition at_ {A} (default : A) (l : list A) (j : N) : A :=
  nth (N.to_nat j) l default.

(** Matches j1 and j2 are between the same two players,
    in either order. *)
Definition same_pair
  (first_players second_players : list N) (j1 j2 : N)
  : Prop :=
  (at_ 0 first_players j1 = at_ 0 first_players j2 /\
   at_ 0 second_players j1 = at_ 0 second_players j2) \/
  (at_ 0 first_players j1 = at_ 0 second_players j2 /\
   at_ 0 second_players j1 = at_ 0 first_players j2).

(** The skill levels skills (one integer per player)
    explain match j: K beat L iff K is strictly more
    skilled, a draw iff the skills are equal. *)
Definition explains (skills : N -> Z)
  (first_players : list N)
    (wins : list bool) (second_players : list N)
      (j : N) : Prop :=
  if at_ false wins j
  then Z.gt (skills (at_ 0 first_players j)) (skills
    (at_ 0 second_players j))
  else skills (at_ 0 first_players j) = skills
    (at_ 0 second_players j).

(** The list is consistent: some skill levels explain
    every reported match. Otherwise at least one match
    is necessarily falsely reported. *)
Definition consistent (first_players : list N)
  (wins : list bool)
    (second_players : list N) : Prop :=
  exists skills : N -> Z, forall j, j < len first_players ->
    explains skills first_players wins second_players j.

(** [@inside chess_consistent_correct] The statement's
    input bounds and guarantees. *)
Record valid_input (player_count : N)
  (first_players : list N)
    (wins : list bool) (second_players : list N) : Prop := {
  (* 2 <= N <= 50 000 *)
  vi_n : 2 <= player_count <= 50000;
  (* 1 <= M <= 250 000 *)
  vi_m : 1 <= len first_players <= 250000;
  (* the following M lines each consist of an integer K, a
    symbol and
     another integer L *)
  vi_wins_len : len wins = len first_players;
  vi_ls_len : len second_players = len first_players;
  (* 0 <= K, L < N *)
  vi_ks : Forall
    (fun player => player < player_count) first_players;
  vi_ls : Forall
    (fun player => player < player_count) second_players;
  (* there is at most one reported match between any given
    pair of players *)
  vi_one_match : forall j1 j2,
    j1 < len first_players -> j2 < len first_players ->
    same_pair first_players second_players j1 j2 -> j1 = j2;
  (* each player takes part in at least one reported match
    *)
  vi_every_player : forall player, player < player_count ->
    exists j, j < len first_players /\
      (at_ 0 first_players j = player
        \/ at_ 0 second_players j = player);
}.

(** ** Correctness *)

(** [@requirement] [@short must decide whether the
    reported matches are consistent.] The answer: true
    ("consistent") iff the list is consistent. *)
Definition chess_consistent_spec (player_count : N)
  (first_players : list N)
    (wins : list bool) (second_players : list N)
      (output : bool)
    : Prop :=
  match output with
  | true => consistent first_players wins second_players
  | false => ~ consistent first_players wins second_players
  end.

(** ** Interface *)

(** The machine-level interface.
    - Input [player_count]:
    - Input [first_players]:
    - Input [wins]:
    - Input [second_players]:
    - Output [output]: *)
Program chess_consistent :
  uint -> array uint -> array bool -> array uint -> bool.

(** ** Bridge *)

(** [@requirement chess_consistent_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [chess_consistent_spec]. *)
Specification chess_consistent_correct :
  forall (player_count : N) (first_players : list N)
    (wins : list bool)
         (second_players : list N) (player_count_int : uint)
         (first_players_arr : array uint)
           (wins_arr : array bool)
         (second_players_arr : array uint),
  valid_input player_count first_players wins second_players
    ->
  repr player_count_int player_count
    -> repr first_players_arr first_players ->
  repr wins_arr wins
    -> repr second_players_arr second_players ->
  exists output : bool,
    repr (chess_consistent player_count_int
      first_players_arr wins_arr
            second_players_arr) output /\
    chess_consistent_spec player_count first_players wins
      second_players
      output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
