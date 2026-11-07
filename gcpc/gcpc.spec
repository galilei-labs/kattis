(** * Galactic Collegiate Programming Contest *)

(** ** Description *)

(** Track one team's rank as scoring events arrive. Rank teams by problems
    solved in descending order, breaking ties by total penalty in ascending
    order.

    [@kattis gcpc]
    - Difficulty: 4.6
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 100000 teams and 1 to 100000 events.
    - Each event's penalty is from 1 to 1000. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
3 4
2 7
3 5
1 6
1 9
Output:
2
3
2
1
*)

(** ** [@hide] Environment *)
(* @function        gcpc
   @signature       uint -> array uint -> array uint -> array uint
   @math_signature  N -> list N -> list N -> list N
   @summary         [gcpc team_count event_teams event_penalties] replays
                    the events "team event_teams_j solved a problem with
                    penalty event_penalties_j", in order, for teams
                    1..team_count that all start at score (0, 0), and
                    returns, for each i, the rank of team 1 after the
                    first i events: one plus the number of teams with more
                    solved problems, or as many and a smaller total
                    penalty.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The m events are the parallel lists event_teams (the
    teams) and event_penalties (the penalties), the j-th event being
    (event_teams_j, event_penalties_j), as in the input's m lines.
    The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of problems team has solved during the events
    (event_teams, ...). *)
Definition solved (team : N) (event_teams : list N) : N :=
  len (filter (fun event_team => event_team =? team)
    event_teams).

(** The total penalty of team: the sum of the penalties of its events. *)
Definition penalty (team : N)
  (event_teams event_penalties : list N) : N :=
  fold_right N.add 0
    (map (fun '(event_team, event_penalty) =>
            if event_team =? team then event_penalty else 0)
         (combine event_teams event_penalties)).

(** The score of team after the events (event_teams, event_penalties):
    (solved, penalty). *)
Definition score (team : N)
  (event_teams event_penalties : list N)
    : N * N :=
  (solved team event_teams, penalty team event_teams
    event_penalties).

(** Score (solved1, penalty1) is better than (solved2, penalty2):
    solved1 > solved2, or solved1 = solved2 and penalty1 < penalty2. *)
Definition better (score1 score2 : N * N) : bool :=
  let '(solved1, penalty1) := score1 in
  let '(solved2, penalty2) := score2 in
  (solved2 <? solved1) || ((solved1 =? solved2) && (penalty1
    <? penalty2)).

(** The teams 1, 2, ..., team_count. *)
Definition teams (team_count : N) : list N :=
  map N.of_nat (seq 1 (N.to_nat team_count)).

(** The rank of team 1 after the events (event_teams, event_penalties):
    ahead + 1, ahead the number of teams whose score is better. *)
Definition rank (team_count : N)
  (event_teams event_penalties : list N)
    : N :=
  1 + len (filter (fun team => better (score team
    event_teams
            event_penalties)
            (score 1 event_teams
            event_penalties))
                  (teams team_count)).

(** [@inside gcpc_correct] The [valid_input] datatype. *)
Record valid_input (team_count : N)
  (event_teams event_penalties : list N)
    : Prop := {
  (* 1 <= n <= 10^5 is the number of teams (team_count) *)
  vi_n : 1 <= team_count <= 10 ^ 5;
  (* 1 <= m <= 10^5 is the number of events *)
  vi_m : 1 <= len event_teams <= 10 ^ 5;
  (* each event line contains two integers t and p
     (event_teams, event_penalties) *)
  vi_p_len : len event_penalties = len event_teams;
  (* 1 <= t <= n *)
  vi_t : Forall (fun event_team => 1 <= event_team <=
    team_count)
           event_teams;
  (* 1 <= p <= 1000 *)
  vi_p : Forall (fun event_penalty => 1 <= event_penalty <=
    1000)
           event_penalties;
}.

(** ** Correctness *)

(** [@requirement] [@short Output m lines: the i-th is the rank of team
    1 after the first i    events.] Output m lines: the i-th is the
    rank of team 1 after the first i events. *)
Definition gcpc_spec (team_count : N)
  (event_teams event_penalties : list N)
    (output : list N) : Prop :=
  len output = len event_teams /\
  forall i : nat, (i < List.length event_teams)%nat ->
    nth i output 0 =
      rank team_count (firstn (S i) event_teams)
        (firstn (S i) event_penalties).

(** ** Interface *)

(** The [gcpc] program on machine values.
    - Input [team_count]:
    - Input [event_teams]:
    - Input [event_penalties]:
    - Output [output]: *)
Program gcpc : uint -> array uint -> array uint -> array
  uint.

(** ** Bridge *)

(** [@requirement gcpc_spec] [@fold full correctness statement] On valid
    represented inputs, [gcpc] returns a represented output
    satisfying [gcpc_spec]. *)
Specification gcpc_correct :
  forall (team_count : N) (event_teams event_penalties :
    list N)
         (team_count_int : uint)
         (event_teams_arr event_penalties_arr : array uint),
  valid_input team_count event_teams event_penalties ->
  repr team_count_int team_count ->
    repr event_teams_arr event_teams ->
  repr event_penalties_arr event_penalties ->
  exists output : list N,
    repr (gcpc team_count_int event_teams_arr
      event_penalties_arr) output /\
    gcpc_spec team_count event_teams event_penalties output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
