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
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A room is designated by its position in the list (the room
   numbers are distinct); a walking pattern [w] gives, for every ordered
   pair of positions (i, j), the number of people per minute walking from
   room i to room j. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of the room at position i. *)
Definition room (rooms : list N) (i : N) : N := nth (N.to_nat i) rooms 0.

(* f 0 + f 1 + ... + f (n - 1). *)
Fixpoint sum_below (f : N -> N) (n : nat) : N :=
  match n with
  | O => 0
  | S m => sum_below f m + f (N.of_nat m)
  end.

(* The entrance is the position of the lowest-numbered room. *)
Definition entrance (rooms : list N) (s : N) : Prop :=
  s < len rooms /\ forall j, j < len rooms -> room rooms s <= room rooms j.

(* The exit is the position of the highest-numbered room. *)
Definition exit (rooms : list N) (t : N) : Prop :=
  t < len rooms /\ forall j, j < len rooms -> room rooms j <= room rooms t.

(* The number of people per minute that can walk from room i to room j:
   their largest common factor if it is greater than one, and no passage
   (0) otherwise, or from a room to itself. *)
Definition cap (rooms : list N) (i j : N) : N :=
  let p := N.gcd (room rooms i) (room rooms j) in
  if N.eqb i j then 0 else if 1 <? p then p else 0.

(* People leaving room v per minute, and people arriving in it. *)
Definition outflow (rooms : list N) (w : N -> N -> N) (v : N) : N :=
  sum_below (fun j => w v j) (List.length rooms).
Definition inflow (rooms : list N) (w : N -> N -> N) (v : N) : N :=
  sum_below (fun j => w j v) (List.length rooms).

(* A walking pattern from s to t: every passage is used within its limit in
   each direction, and nobody waits in a room other than s and t. *)
Definition is_walk (rooms : list N) (s t : N) (w : N -> N -> N) : Prop :=
  (forall i j, i < len rooms -> j < len rooms -> w i j <= cap rooms i j) /\
  (forall v, v < len rooms -> v <> s -> v <> t ->
     outflow rooms w v = inflow rooms w v).

(* The number of people per minute entering the maze at s. *)
Definition entering (rooms : list N) (s : N) (w : N -> N -> N) : Z :=
  (Z.of_N (outflow rooms w s) - Z.of_N (inflow rooms w s))%Z.

(* The statement's bounds. *)
Record valid_input (rooms : list N) : Prop := {
  (* an integer 2 <= n <= 1000 indicating the number of rooms *)
  vi_n : 2 <= len rooms <= 1000;
  (* each room number is in the range [2, 2 * 10^9] *)
  vi_range : Forall (fun r => 2 <= r <= 2 * 10 ^ 9) rooms;
  (* n unique integers *)
  vi_unique : NoDup rooms;
  (* no maze supports more than 10^9 people entering per minute *)
  vi_answer : forall s t w, entrance rooms s -> exit rooms t ->
    is_walk rooms s t w -> (entering rooms s w <= 10 ^ 9)%Z;
}.

(* The answer is the maximum number of people entering: some walking
   pattern reaches it, and none exceeds it. *)
Definition mazemovement_spec (rooms : list N) (ans : N) : Prop :=
  forall s t, entrance rooms s -> exit rooms t ->
    (exists w, is_walk rooms s t w /\ entering rooms s w = Z.of_N ans) /\
    (forall w, is_walk rooms s t w -> (entering rooms s w <= Z.of_N ans)%Z).

Program mazemovement : array uint -> uint.

Specification mazemovement_correct : forall (rooms : list N) (x : array uint),
  valid_input rooms -> repr x rooms ->
  exists ans : N, repr (mazemovement x) ans /\ mazemovement_spec rooms ans.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
