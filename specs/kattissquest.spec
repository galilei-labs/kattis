(* @function        kattissquest
   @signature       array command -> array uint
   @math_signature  list op -> list N
   @summary         [kattissquest cs] runs the commands in order over a pool
                    of quests, initially empty: [add E G] puts one more quest
                    of energy E and gold G in the pool; [query X] runs Kattis's
                    greedy session with energy X (repeatedly clear the quest of
                    largest energy <= the energy left, ties by largest gold,
                    removing it from the pool and subtracting its energy) and
                    prints the gold earned.  The result holds the printed
                    golds, one per query, in order.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Permutation.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* One input line, already parsed: "add E G" or "query X"; [command] on the
   machine side, [op] on the math side, related field by field. *)
Inductive command : Set :=
| Add (e g : uint)
| Query (x : uint).

Inductive op : Set :=
| add (e g : N)
| query (x : N).

Instance repr_command : Repr command op :=
  fun c o => match c, o with
             | Add e g, add e' g' => repr e e' /\ repr g g'
             | Query x, query x' => repr x x'
             | _, _ => False
             end.

(* Math side.  A quest is (energy, gold); the pool is a multiset of quests,
   as a list taken up to permutation. *)

Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The quests of the add commands, and the energies of the query commands. *)
Definition adds (cs : list op) : list (N * N) :=
  flat_map (fun c => match c with add e g => [(e, g)] | query _ => [] end) cs.
Definition queries (cs : list op) : list N :=
  flat_map (fun c => match c with query x => [x] | add _ _ => [] end) cs.

(* [q] is the quest step 1 picks with energy [x]: among the quests of the
   pool of energy <= x, the largest energy, ties by the largest gold. *)
Definition chosen (pool : list (N * N)) (x : N) (q : N * N) : Prop :=
  In q pool /\ fst q <= x /\
  forall q', In q' pool -> fst q' <= x ->
    fst q' < fst q \/ (fst q' = fst q /\ snd q' <= snd q).

(* [session pool x gold pool']: the greedy session with energy [x] on
   [pool] earns [gold] and leaves [pool']; it stops when no quest of the
   pool has energy <= the energy left (in particular when that is 0). *)
Inductive session : list (N * N) -> N -> N -> list (N * N) -> Prop :=
| session_stop : forall pool x,
    (forall q, In q pool -> x < fst q) ->
    session pool x 0 pool
| session_step : forall pool x q rest gold pool',
    chosen pool x q ->
    Permutation pool (q :: rest) ->
    session rest (x - fst q) gold pool' ->
    session pool x (snd q + gold) pool'.

(* [runs pool cs answers]: the commands [cs], run from [pool], print
   [answers] (one per query, in order). *)
Inductive runs : list (N * N) -> list op -> list N -> Prop :=
| runs_nil : forall pool, runs pool [] []
| runs_add : forall pool e g cs answers,
    runs ((e, g) :: pool) cs answers ->
    runs pool (add e g :: cs) answers
| runs_query : forall pool x cs gold pool' answers,
    session pool x gold pool' ->
    runs pool' cs answers ->
    runs pool (query x :: cs) (gold :: answers).

(* The statement's bounds. *)
Record valid_input (cs : list op) : Prop := {
  (* 1 <= N <= 2 * 10^5, the number of commands *)
  vi_n : 1 <= len cs <= 2 * 10 ^ 5;
  (* 1 <= E, G <= 10^5 *)
  vi_e : Forall (fun q => 1 <= fst q <= 10 ^ 5) (adds cs);
  vi_g : Forall (fun q => 1 <= snd q <= 10 ^ 5) (adds cs);
  (* 1 <= X <= 10^5 *)
  vi_x : Forall (fun x => 1 <= x <= 10 ^ 5) (queries cs);
}.

(* The answers are what the commands print, starting from the empty pool. *)
Definition kattissquest_spec (cs : list op) (answers : list N) : Prop :=
  runs [] cs answers.

Program kattissquest : array command -> array uint.

Specification kattissquest_correct : forall (cs : list op) (x : array command),
  valid_input cs -> repr x cs ->
  exists answers : list N,
    repr (kattissquest x) answers /\ kattissquest_spec cs answers.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
