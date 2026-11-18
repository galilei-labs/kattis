(** * Galactic Collegiate Programming Contest *)

(** ** Description *)

(** Follow team one's rank in a programming contest. Initially every team
    has solved no problems and has zero penalty. Each event reports that a
    team solved one problem and gives the penalty added to its total.
    More solved problems rank ahead; among teams with the same solved count,
    lower total penalty ranks ahead. A team's rank is one plus the number
    of teams strictly ahead of it, so tied scores share a rank. Report team
    one's rank after every event, including events for other teams.

    [@kattis gcpc]
    - Difficulty: 4.7
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Team count: $1 \le n \le 10^{5}$ and Event count: $1 \le m \le 10^{5}$.
    - Each event's penalty: $1 \le p \le 10^{3}$. *)

(** ** Examples *)

(** - Input convention: Team and event counts, followed by team-penalty pairs in chronological order.
    - Output convention: Team 1's rank after each event, one rank per line. *)
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
                    It runs in at most c1 * (n + m + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of teams and m of events (one deletion, one insertion
                    and one rank query per event on the balanced order-
                    statistic tree, each within its depth, logarithmic by
                    the balance invariant), for two constants c1, c2.
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

(** The number of problems solved by [team] in the supplied event prefix. *)
Definition solved (team : N) (event_teams : list N) : N :=
  len (filter (fun event_team => event_team =? team)
    event_teams).

(** The total penalty accumulated by [team] in the supplied event prefix. *)
Fixpoint penalty (team : N)
  (event_teams event_penalties : list N) : N :=
  match event_teams, event_penalties with
  | event_team :: teams, event_penalty :: penalties =>
      (if event_team =? team then event_penalty else 0) + penalty team teams penalties
  | _, _ => 0
  end.

(** The pair of solved-problem count and total penalty for [team] after the supplied
    events. *)
Definition score (team : N)
  (event_teams event_penalties : list N)
    : N * N :=
  (solved team event_teams, penalty team event_teams
    event_penalties).

(** [score1] ranks ahead of [score2]: more solved problems, or equal solved counts
    and a smaller total penalty. *)
Definition better (score1 score2 : N * N) : bool :=
  let '(solved1, penalty1) := score1 in
  let '(solved2, penalty2) := score2 in
  (solved2 <? solved1) || ((solved1 =? solved2) && (penalty1
    <? penalty2)).

(** The teams 1, 2, ..., [team_count]. *)
Definition teams (team_count : N) : list N :=
  map N.of_nat (seq 1 (N.to_nat team_count)).

(** One plus the number of teams whose score is better than team one's score after
    the supplied events. *)
Definition rank (team_count : N)
  (event_teams event_penalties : list N)
    : N :=
  1 + len (filter (fun team => better (score team
    event_teams
            event_penalties)
            (score 1 event_teams
            event_penalties))
                  (teams team_count)).

(** [@inside gcpc_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
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
  (* 1 <= p <= 10^3 *)
  vi_p : Forall (fun event_penalty => 1 <= event_penalty <=
    1000)
           event_penalties;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry is team 1's rank after the corresponding event, ordered by
    decreasing solved count and increasing penalty. *)
Definition gcpc_spec (team_count : N)
  (event_teams event_penalties : list N)
    (output : list N) : Prop :=
  len output = len event_teams /\
  forall i : nat, (i < List.length event_teams)%nat ->
    nth i output 0 =
      rank team_count (firstn (S i) event_teams)
        (firstn (S i) event_penalties).

(** ** Complexity *)

(** [@requirement] Runs in $O((n+m+1)\log(n+2))$ steps, where $n$ is the number of teams and $m$ the number of events. *)
Definition gcpc_time_spec (c1 c2 n_team_count n_event_teams steps : nat) : Prop :=
  (steps <= c1 * ((n_team_count + n_event_teams + 1) * (Nat.log2 (n_team_count) + 1)) + c2)%nat.

(** ** Interface *)

(** Report team one's contest rank after each solved-problem event. More
    solved problems rank ahead, then lower total penalty; tied scores share
    a rank, equal to one plus the number of teams strictly ahead.
    - Input [team_count]: Number of teams in the ranking.
    - Input [event_teams]: Team credited with a solution at each event.
    - Input [event_penalties]: Penalty added by each corresponding event.
    - Output [output]: Each output entry is team 1's rank after the corresponding event, ordered by decreasing solved count and increasing penalty. *)
Program gcpc : uint -> array uint -> array uint -> array
  uint.

(** [@example gcpc]
    - Sample: 1
    - Input [team_count]: 3
    - Input [event_teams]: [2; 3; 1; 1]
    - Input [event_penalties]: [7; 5; 6; 9]
    - Output [output]: [2; 3; 2; 1]
*)

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

(** ** Complexity *)

(** [@hide] [gcpc_cost] is the cost translation of [gcpc] (the judge
    recomputes it and compares) ... *)
Complexity gcpc_cost for gcpc.

(** [@fold complexity bound] ... and runs in at most c1 * (n + m + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of teams and m of events (one deletion, one insertion and one rank query per event on the balanced order-statistic tree, each within its depth, logarithmic by the balance invariant), for two constants
    quantified before the inputs, on every valid input. [@requirement gcpc_time_spec] *)
Specification gcpc_time : exists c1 c2 : nat,
  forall (team_count : N) (event_teams event_penalties :
  list N)
  (team_count_int : uint)
  (event_teams_arr event_penalties_arr : array uint),
  valid_input team_count event_teams event_penalties ->
  repr team_count_int team_count ->
  repr event_teams_arr event_teams ->
  repr event_penalties_arr event_penalties ->
  gcpc_time_spec c1 c2 (size team_count_int) (size event_teams_arr) (cost3 gcpc_cost team_count_int event_teams_arr event_penalties_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
