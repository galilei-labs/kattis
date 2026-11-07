(** * Kattis's Quest *)

(** ** Description *)

(** Maintain tasks with energy costs and rewards. For each budget query,
    repeatedly remove the affordable task with greatest cost, breaking ties
    by greatest reward, and return the total reward earned.

    [@kattis kattissquest]
    - Difficulty: 4.0
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 200000 commands.
    - Task energy, reward and query budget are from 1 to 100000. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Permutation.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** One input line, already parsed: "add E G" or "query X"; [command] on
    the machine side, [op] on the math side, related field by field. *)
Inductive command : Set :=
| Add (energy gold : uint)
| Query (energy : uint).

(** The [op] datatype. *)
Inductive op : Set :=
| add (energy gold : N)
| query (energy : N).

Instance repr_command : Repr command op :=
  fun machine_command math_command =>
    match machine_command, math_command with
    | Add energy_int gold_int, add energy gold =>
        repr energy_int energy /\ repr gold_int gold
    | Query energy_int, query energy => repr energy_int
      energy
    | _, _ => False
    end.

(** Math side. A quest is (energy, gold); the pool is a multiset of
    quests, as a list taken up to permutation. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The quests of the add commands, and the energies of the query
    commands. *)
Definition adds (commands : list op) : list (N * N) :=
  flat_map (fun instruction => match instruction with
            | add energy gold =>
            [(energy, gold)]
            | query _ => []
            end) commands.
(** The [queries] definition. *)
Definition queries (commands : list op) : list N :=
  flat_map (fun instruction => match instruction with
            | query energy => [energy]
            | add _ _ => []
            end) commands.

(** [quest] is the quest step 1 picks with energy [energy]: among the
    quests of the pool of energy at most [energy], the largest
    energy, ties by the largest gold. *)
Definition chosen (pool : list (N * N)) (energy : N)
  (quest : N * N) : Prop :=
  In quest pool /\ fst quest <= energy /\
  forall quest', In quest' pool -> fst quest' <= energy ->
    fst quest' < fst quest \/
    (fst quest' = fst quest /\ snd quest' <= snd quest).

(** [session pool energy gold pool']: the greedy session with energy
    [energy] on [pool] earns [gold] and leaves [pool']; it stops
    when no quest of the pool has energy <= the energy left (in
    particular when that is 0). *)
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

(** [@inside kattissquest_correct] The statement's bounds. *)
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

(** [@requirement] [@short The output is what the commands print,
    starting from the empty    pool.] The output is what the
    commands print, starting from the empty pool. *)
Definition kattissquest_spec (commands : list op)
  (output : list N)
    : Prop :=
  runs [] commands output.

(** ** Interface *)

(** The [kattissquest] program on machine values.
    - Input [commands]:
    - Output [output]: *)
Program kattissquest : array command -> array uint.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
