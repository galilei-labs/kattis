(** * Kattis's Quest *)

(** ** Description *)

(** Maintain an initially empty collection of quests. Each quest has an energy
    cost and a gold reward. Process two kinds of commands in order:

    - [add E G]: Add a quest costing [E] energy and rewarding [G] gold.
    - [query X]: Start with a fresh budget of [X] energy. Repeatedly complete
      the affordable quest with the highest cost, breaking ties by the highest
      reward. Deduct its cost from the remaining budget, collect its reward,
      and remove it from the collection. Stop when no remaining quest is
      affordable, and output the total gold collected.

    Completed quests stay removed; uncompleted quests remain available for
    later queries.

    [@kattis kattissquest]
    - Difficulty: 4.0
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Command count: $1 \le q \le 2 \times 10^{5}$.
    - Quest cost, reward and query budget: $1 \le E, G, X \le 10^{5}$. *)

(** ** Examples *)

(** - Input convention: Command count, followed by add energy reward or query budget commands.
    - Output convention: One total reward per query command. *)
(* Input:
9
add 8 10
add 3 25
add 5 6
query 7
query 7
add 1 9
add 2 13
query 20
query 1
Output:
6
25
32
0
*)

(** ** [@hide] Environment *)
(* @function        kattissquest
   @signature       array command -> array uint
   @math_signature  list op -> list N
   @summary         [kattissquest commands] runs the commands in order over
                    a pool of quests, initially empty: [add E G] puts one
                    more quest of energy E and gold G in the pool; [query X]
                    runs Kattis's greedy session with energy X (repeatedly
                    clear the quest of largest energy <= the energy left,
                    ties by largest gold, removing it from the pool and
                    subtracting its energy) and prints the gold earned.  The
                    result, output, holds the printed golds, one per
                    query, in order.
                    It runs in at most c1 * (U + (N + 1) * (log2 N + log2
                    log2 U + 1)) + c2 steps of the cost model on a valid
                    input, N the number of commands and U the largest value
                    they carry ([max_size], an upper bound of the energy
                    universe): the van Emde Boas tree costs U to build and
                    log log U per operation, the gold heaps log N per
                    operation, and the quests cleared over a call are at
                    most the quests added, for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Permutation.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** One input line, already parsed: "add E G" or "query X"; [command] on
    the machine side, [op] in the specification, related field by field. *)
Inductive command : Set :=
| Add (energy gold : uint)
| Query (energy : uint).

(** A mathematical command: add a quest with its energy cost and gold reward, or
    query with an available energy budget. *)
Inductive op : Set :=
| add (energy gold : N)
| query (energy : N).

(** [@hide] The representation relation between machine and mathematical commands. *)
Instance repr_command : Repr command op :=
  fun machine_command math_command =>
    match machine_command, math_command with
    | Add energy_int gold_int, add energy gold =>
        repr energy_int energy /\ repr gold_int gold
    | Query energy_int, query energy => repr energy_int
      energy
    | _, _ => False
    end.

(** [@hide] The cost translation of [command], the witness of a machine
    command and its size (the largest value it carries), for the bound below. *)
Elpi complexity command.
Instance witness_command : Witness command (fun CM c => command_cost CM c) :=
  fun c => match c with
           | Add e g => Add_cost stepsCM e (witness e) g (witness g)
           | Query e => Query_cost stepsCM e (witness e)
           end.
Instance witness_array_command :
  Witness (array command) (fun CM t => array_cost CM command (command_cost CM) t) :=
  @witness_array command (fun CM => command_cost CM) witness_command.
Instance size_command : Size command :=
  fun c => match c with Add e g => Nat.max (size e) (size g) | Query e => size e end.

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The energy-cost and gold-reward pairs of the add commands, in command order. *)
Definition adds (commands : list op) : list (N * N) :=
  flat_map (fun instruction => match instruction with
            | add energy gold =>
            [(energy, gold)]
            | query _ => []
            end) commands.
(** The energy budgets of the query commands, in command order. *)
Definition queries (commands : list op) : list N :=
  flat_map (fun instruction => match instruction with
            | query energy => [energy]
            | add _ _ => []
            end) commands.

(** [chosen pool energy quest] means that [quest] is the next quest to complete
    from [pool] with budget [energy]. Among affordable quests, choose the one
    with the highest cost, breaking ties by the highest reward. *)
Definition chosen (pool : list (N * N)) (energy : N)
  (quest : N * N) : Prop :=
  In quest pool /\ fst quest <= energy /\
  forall quest', In quest' pool -> fst quest' <= energy ->
    fst quest' < fst quest \/
    (fst quest' = fst quest /\ snd quest' <= snd quest).

(** [session pool energy gold pool'] describes one query: start with quests
    [pool] and budget [energy], repeatedly complete the quest selected by
    [chosen], deduct its cost, and collect its reward. Stop when no remaining
    quest is affordable. The total reward is [gold], and the remaining quests
    are [pool']. *)
Inductive session : list (N * N) -> N -> N -> list
  (N * N) -> Prop :=
| session_stop : forall pool energy,
    (forall quest, In quest pool -> energy < fst quest) ->
    session pool energy 0 pool
| session_step : forall pool energy quest rest gold pool',
    chosen pool energy quest ->
    Permutation pool (quest :: rest) ->
    session rest (energy - fst quest) gold pool' ->
    session pool energy (snd quest + gold) pool'.

(** [runs pool commands answers]: the commands [commands], run from
    [pool], print [answers] (one per query, in order). *)
Inductive runs : list
  (N * N) -> list op -> list N -> Prop :=
| runs_nil : forall pool, runs pool [] []
| runs_add : forall pool energy gold commands answers,
    runs ((energy, gold) :: pool) commands answers ->
    runs pool (add energy gold :: commands) answers
| runs_query : forall pool energy commands gold pool'
  answers,
    session pool energy gold pool' ->
    runs pool' commands answers ->
    runs pool (query energy :: commands) (gold :: answers).

(** [@inside kattissquest_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (commands : list op) : Prop := {
  (* 1 <= N <= 2 * 10^5, the number of commands *)
  vi_n : 1 <= len commands <= 2 * 10 ^ 5;
  (* 1 <= E, G <= 10^5 *)
  vi_e : Forall (fun quest => 1 <= fst quest <= 10 ^ 5)
    (adds commands);
  vi_g : Forall (fun quest => 1 <= snd quest <= 10 ^ 5)
    (adds commands);
  (* 1 <= X <= 10^5 *)
  vi_x : Forall (fun energy => 1 <= energy <= 10 ^ 5)
    (queries commands);
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the total reward for each budget query under the specified greedy
    quest-selection rule, starting with an empty quest collection. *)
Definition kattissquest_spec (commands : list op)
  (output : list N)
    : Prop :=
  runs [] commands output.

(** ** Complexity *)

(** [@requirement] Runs in $O(U+1+(n+1)(\log(n+2)+\log\log(U+4)))$ steps, where $n$ is the number of commands and $U$ the largest numeric value carried by any command. *)
Definition kattissquest_time_spec (c1 c2 max_commands n_commands steps : nat) : Prop :=
  (steps <= c1 * (max_commands + 1 + (n_commands + 1) * (Nat.log2 (n_commands) + Nat.log2 (Nat.log2 (max_commands + 1) + 1) + 1)) + c2)%nat.

(** ** Interface *)

(** Maintain quests with energy costs and rewards. For each budget query, repeatedly remove
    the affordable quest with greatest cost, breaking ties by greatest reward, and return
    the total reward earned.
    - Input [commands]: Quest additions and budget queries in execution order.
    - Output [output]: The output gives the total reward for each budget query under the specified greedy quest-selection rule, starting with an empty quest collection. *)
Program kattissquest : array command -> array uint.

(** [@example kattissquest]
    - Sample: 1
    - Input [commands]: [add 8 10; add 3 25; add 5 6; query 7; query 7; add 1 9; add 2 13; query 20; query 1]
    - Output [output]: [6; 25; 32; 0]
*)

(** ** Bridge *)

(** [@requirement kattissquest_spec] [@fold full correctness statement]
    On valid represented inputs, [kattissquest] returns a
    represented output satisfying [kattissquest_spec]. *)
Specification kattissquest_correct :
  forall (commands : list op) (commands_arr : array
    command),
  valid_input commands -> repr commands_arr commands ->
  exists output : list N,
    repr (kattissquest commands_arr) output /\
    kattissquest_spec commands output.

(** ** Complexity *)

(** [@hide] [kattissquest_cost] is the cost translation of [kattissquest] (the judge
    recomputes it and compares) ... *)
Complexity kattissquest_cost for kattissquest.

(** [@fold complexity bound] ... and runs in at most c1 * (U + (N + 1) * (log2 N + log2 log2 U + 1)) + c2 steps of the cost model on a valid input, N the number of commands and U the largest value they carry ([max_size], an upper bound of the energy universe): the van Emde Boas tree costs U to build and log log U per operation, the gold heaps log N per operation, and the quests cleared over a call are at most the quests added, for two constants
    quantified before the inputs, on every valid input. [@requirement kattissquest_time_spec] *)
Specification kattissquest_time : exists c1 c2 : nat,
  forall (commands : list op) (commands_arr : array
  command),
  valid_input commands -> repr commands_arr commands ->
  kattissquest_time_spec c1 c2 (max_size commands_arr) (size commands_arr) (cost1 kattissquest_cost commands_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
